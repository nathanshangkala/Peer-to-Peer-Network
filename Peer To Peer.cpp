#include <sys/types.h>
#include <sys/socket.h>

#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>

#include <sys/stat.h>

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <signal.h>
#include <fcntl.h>
#include <condition_variable>
#include <set>
#include <map>
#include <string>
#include <list>
#include <thread>
#include <sstream>
#include <sstream>
#include <vector>
#include <fstream>
#include <iostream>
#include <mutex>
#include <queue>
#include <utility>
#include <climits>

#include <sys/time.h>
#include <openssl/sha.h>
#include <algorithm>

#define SOFT_STATE 0


using namespace std;

static
void get_timestamp(char timestamp_buf[32])
{
    struct timeval now;
    char time_buf[26];
    int i;

    gettimeofday(&now, NULL);
    strcpy(time_buf, ctime(&now.tv_sec));
    for (i=0; i < 11; i++) {
        timestamp_buf[i] = time_buf[i];
    }
    timestamp_buf[11] = time_buf[20];
    timestamp_buf[12] = time_buf[21];
    timestamp_buf[13] = time_buf[22];
    timestamp_buf[14] = time_buf[23];
    for (i=15; i < 24; i++) {
        timestamp_buf[i] = time_buf[i-5];
    }
    sprintf(&timestamp_buf[24], ".%06d", (int)now.tv_usec);
}

//TODO Check valgrind errors that might come Connection class

static bool server_state;
static int sleep_time_neigh= 0;
static string master_node_id= "";
static string master_port= "";
static string master_host= "";
static int master_connection = 1;
static int max_ttl = 0;
static int msg_lifetime = 0;
static struct timeval start_time;
static bool connection_quits = false; 

//for logging
static bool IsLoggingSAYHELLO = false; 
static bool IsLoggingLSUPDATE = false; 
static bool IsLoggingUCASTAPP = false; 
static int log_file_dec;

struct node
{
    //first is vertex & second is cost
    node(string node_id, int cost)
    {
        vertex_cost = make_pair(node_id, cost);
        pred = nullptr;
        level  =-1;
        next_hop = nullptr;
    }
    //Keeps track shortest distance from src to i
    pair<string, int> vertex_cost;
    node* pred;
    node* next_hop;
    int level = -1;
};

class Connection
{
public:
    Connection(int socketnumber, int connection_number)
    {
        this->bSent = bSent;
        this->socketnumber = socketnumber;
        this->connection_number = connection_number;
        m = make_shared<mutex>();
        cv_con = make_shared<condition_variable>();
    };
    ~Connection(){};
    int bSent;
    int socketnumber;
    int connection_number;
    // -1 -> closed by console
    // -2 -> closed by connection hadnling threads
    shared_ptr<thread> read_thread;
    shared_ptr<thread> write_thread;
    void SetThread(shared_ptr<thread> read, shared_ptr<thread> write)
    {
        this->read_thread = read;
        this->write_thread = write;
    }
    shared_ptr<mutex > m;
    shared_ptr<condition_variable> cv_con;

    //contains messgae
    queue<shared_ptr<string > >q;

    int state;
    //state 0 -> connection created from accept 
    //no neighbor_nodeid
    //state 1 -> connection created by Neighbor Thread
    //already know neighbor_nodeid
    // char neighbor_nodeid [40];
    vector<string> neighbor_nodeid;
    //add message to work queue for write_thr
    //dont touch mutex_m
    void AddWork(shared_ptr<string> msg)
    {
        m->lock();
        q.push(msg);
        cv_con->notify_all();
        m->unlock();
    }
    shared_ptr<string > WaitForWork()
    {
        unique_lock<mutex> l(*m);
        if(!server_state)
            return nullptr;
        while (q.empty())
        {
            cv_con->wait(l);
            if(q.size()>0)
                break;
        }
        shared_ptr<string > ret = q.front();
        q.pop();
        return ret;
    }
    string connection_origin ="";
    bool CanLSUpdate = false; 
};

static vector<pair<string, vector<node*> > > adj_list;
static map<int, string> message_cache;
static vector<map<string, map<string, string> > > config;
static map<int,shared_ptr<Connection > > connection_info;
static vector<string> active_neigh;

static
vector<node*> forwarding(bool IsPrint)
{
    vector<pair <node*, vector<node* > > > adj;
    for(unsigned int i = 0; i < adj_list.size(); i++)
    {
        string first = adj_list[i].first;
        vector<node*> second = adj_list[i].second;
        node* n = new node(first,1 );
        adj.push_back(make_pair(n, second));
    }
    queue<int> q;
    adj[0].first->level = 0;
    q.push(0);
    while(!q.empty())
    {
        int v  = q.front();
        q.pop();
        for(unsigned int u = 0 ; u < adj[v].second.size(); u++)
        {
            for(unsigned int j = 0 ; j < adj.size(); j++)
            {
                if(adj[j].first->vertex_cost.first == adj_list[v].second[u]->vertex_cost.first)
                {
                    if(adj[j].first->level== -1)
                    {
                        adj[j].first->level = 0;
                        adj[j].first->pred = adj[v].first;
                        q.push(j);
                    }
                }
            }
        }
    }

    node* start_node= adj[0].first;
    vector<node*> ret;
    for(unsigned int i = 0 ; i < adj.size(); i++)
    {
        node* v = adj[i].first;
        if(v->pred == nullptr)
        {
            v->next_hop = nullptr;
        }
        else if(v->pred == start_node)
        {
            v->next_hop = v;
        }
        else
        {
            node* u = v;
            while(v->pred->pred)
            {
                if(v->pred->pred == start_node)
                    break;
                v = v->pred;
            }
            u->next_hop = v->pred;
            v = u;
        }
        ret.push_back(v);
    }

    if(IsPrint)
    {
        cout << "Forwarding table of " << master_node_id << ":\n";
        for(unsigned int i = 0 ;  i < ret.size(); i++)
        {
            if(ret[i]->vertex_cost.first != master_node_id)
            {
                if(ret[i]->next_hop)
                {
                    cout << "\t" << ret[i]->vertex_cost.first << ": " << ret[i]->next_hop->vertex_cost.first;
                }
            }
            cout << endl;
        }
    }

    return ret;
}

string GetTarget(string destination)
{
    string target ="";
    // cout << "DEBUG GET TARGET\n";
    // cout << "DESTINATION " << destination << endl;
    vector<node*> ret = forwarding(false);
    for(unsigned int i = 0 ; i < ret.size(); i++)
    {
        if(ret[i]->vertex_cost.first == destination)
        {
            for(unsigned int j = 0 ; j < active_neigh.size(); j++)
            {
                // if(active_neigh[j] == ret[i]->vertex_cost.first)
                // {
                    target =ret[i]->next_hop->vertex_cost.first;
                    return target; 
                // }
            }
        }
    }
    return target;
}

static 
set<node*> BFS(node* start)
{
    vector<bool> visited;
    visited.resize(adj_list.size());
    for(unsigned int i = 0 ; i < visited.size(); i++)
        visited[i] = false;
    int x = -1;
    list<string> queue;
    set<node*> visited_nodes;
    for(unsigned int i = 0 ; i < adj_list.size(); i++)
    {
        if (adj_list[i].first == start->vertex_cost.first)
        {
            x = i;
            visited[i] = true;
            queue.insert(queue.begin(), adj_list[i].first);
        }
    }

    while(!queue.empty())
    {
        string curr = queue.front();
        vector<node*> adj_nodes= adj_list[x].second;
        visited_nodes.insert(new node(curr, 1));
        queue.pop_front();
        vector<string> to_make;
        for(unsigned int i =0 ; i < adj_nodes.size(); i++)
        {
            to_make.push_back(adj_nodes[i]->vertex_cost.first);
            for(unsigned int f = 0 ; f < adj_list.size(); f++)
            {
                if(adj_list[f].first == adj_nodes[i]->vertex_cost.first)
                {
                    x=f;
                }
            }            

            if(!visited[x])
            {
                visited[x] = true;
                for(unsigned int i = 0 ; i < to_make.size(); i++)
                {
                    queue.push_back(to_make[i]);
                }
            }
        }
    }
    return visited_nodes;
}

static
void PrintAjdList()
{
    for(unsigned int i = 0 ; i < adj_list.size(); i++)
    {
        cout << adj_list[i].first << ": ";
        for(unsigned int j = 0 ; j < adj_list[i].second.size(); j++)
        {
            cout << adj_list[i].second[j]->vertex_cost.first;
            if(j != adj_list[i].second.size()-1)
            {
                 cout << ", ";
            }
        }
        cout << endl;
    }
    cout << endl;
}

static 
int read_a_line(int client_socket_fd, char buf[], string &res)
{
    char temp ='\0';
    int i= 0;
    for(;;)
    {
        if(temp == '\r')
        {
            int x = read(client_socket_fd, &temp, 1);
            if(x<=0)
                return -1;
            i++;
            break;
        }
        else
        {
            int x = read(client_socket_fd, &temp, 1);
            if(x<=0)
                return -1;
            res+= temp;
            buf[i]= temp;
        }
        i++;
    }
    return i;
}

static
void GetObjID(
        char node_id[40],
        const char *obj_category,
        char hexstring_of_unique_obj_id[(SHA_DIGEST_LENGTH<<1)+1],
        char origin_start_time[18])
{
    static unsigned long seq_no=0L;
    static struct timeval node_start_time;

    if (seq_no++ == 0L) {
        gettimeofday(&node_start_time, NULL);
    }
#if SOFT_STATE
    static char hexchar[]="0123456789abcdef";
    char unique_str[128];
    char returned_obj_id[SHA_DIGEST_LENGTH];

    snprintf(unique_str, sizeof(unique_str), "%s_%d_%s_%1ld",
            node_id, (int)(node_start_time.tv_sec), obj_category, (long)seq_no);
    SHA1((unsigned char *)unique_str, strlen(unique_str), (unsigned char *)returned_obj_id);
    for (int i=0; i < SHA_DIGEST_LENGTH; i++) {
        unsigned char ch=(unsigned char)returned_obj_id[i];
        int hi_nibble=(int)(unsigned int)((ch>>4)&0x0f);
        int lo_nibble=(int)(unsigned int)(ch&0x0f);

        hexstring_of_unique_obj_id[i<<1] = hexchar[hi_nibble];
        hexstring_of_unique_obj_id[(i<<1)+1] = hexchar[lo_nibble];
    }
    hexstring_of_unique_obj_id[SHA_DIGEST_LENGTH<<1] = '\0';
#else /* ~SOFT_STATE */
    struct timeval now;
    gettimeofday(&now, NULL);
    /* [BC: fixed 4/10/2019] */
    snprintf(hexstring_of_unique_obj_id, (SHA_DIGEST_LENGTH<<1)+1,
            "%s_%010d.%06d", node_id, (int)(now.tv_sec), (int)(now.tv_usec));
#endif /* SOFT_STATE */
    snprintf(origin_start_time, 18, "%010d.%06d", (int)(node_start_time.tv_sec), (int)(node_start_time.tv_usec));
}

static 
void InitialLSUPDATE(string from, shared_ptr<Connection> c)
{
    string check = master_node_id;
    check += ",";

    string temp = "353NET/1.0 LSUPDATE NONE/1.0\r\n";
    temp += "TTL: ";
    temp += to_string(max_ttl);
    temp += "\r\n";
    temp += "MessageID: ";

    char node_id[40];
    strcpy (node_id, from.c_str());
    string obj_category = "LSUPDATE";
    char hexstring_of_unique_obj_id[(SHA_DIGEST_LENGTH<<1)+1];
    char origin_start_time[18];
    GetObjID(node_id, obj_category.c_str(), hexstring_of_unique_obj_id, origin_start_time);
    
    // string x =from;
    // x+= ":";
    // x += master_node_id;
    temp += obj_category;
    temp += "\r\n";
    temp += "From: ";
    temp += from;
    temp += "\r\n";
    temp += "OriginStartTime: ";
    temp += origin_start_time;
    temp += "\r\n";
    temp += "Content-Length: ";
    temp += to_string(check.length());
    temp += "\r\n\r\n";
    temp += check;

    vector<node*> temp_n;
    if(adj_list.size()<=0)
    {
        temp_n.push_back(new node(from, 1));
        adj_list.push_back(make_pair(master_node_id, temp_n));
    }
    // else
    //     adj_list[0].second.push_back(new node(from, 1));

    message_cache.insert(pair<int,string>(message_cache.size(), obj_category));

    shared_ptr<string> w2 = make_shared<string>(temp);
    // mutex_m.lock();
    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        shared_ptr<Connection> c_q = it->second;
        if(c_q->socketnumber >=0 && c_q->state == 1)
        {
            c_q->AddWork(w2);
        }
    }
}

static
void floodLSUDPATEMessage(int tmp, string from, string message_id, set<string> neighbors, shared_ptr<Connection> c)
{
    string check="";
    for(auto it = neighbors.begin() ; it != neighbors.end(); it++)
    {
        check += *it;
        check += ",";
    }
    string temp2 = "353NET/1.0 LSUPDATE NONE/1.0\r\n";
    temp2 += "TTL: ";
    temp2 += to_string(tmp);
    temp2 += "\r\n";

    temp2 += "Flood: 1";
    temp2 += "\r\n";

    temp2 += "MessageID: ";
    char node_id[40];
    strcpy (node_id, from.c_str());
    string obj_category ="LSUPDATE";
    char hexstring_of_unique_obj_id[(SHA_DIGEST_LENGTH<<1)+1];
    char origin_start_time[18];
    GetObjID(node_id, obj_category.c_str(), hexstring_of_unique_obj_id, origin_start_time);
    temp2 += hexstring_of_unique_obj_id;
    message_cache.insert(pair<int,string>(message_cache.size(), hexstring_of_unique_obj_id));
    temp2 += "\r\n";
    temp2 += "From: ";
    temp2 += from;
    temp2 += "\r\n";
    temp2 += "OriginStartTime: ";
    temp2 += origin_start_time;
    temp2 += "\r\n";
    temp2 += "Content-Length: ";
    temp2 += to_string(check.length());
    temp2 += "\r\n\r\n";
    temp2+=check;
    shared_ptr<string> w = make_shared<string>(temp2);
    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        shared_ptr<Connection> c_q = it->second;
        if(c_q !=c)
        {
            if(c_q->state == 1 && c_q->socketnumber>0 && c_q->CanLSUpdate && c_q->connection_origin!=from)
            {
                if(IsLoggingLSUPDATE)
                {
                    char timestamp_buf[32];
                    get_timestamp(timestamp_buf);
                    string log = "[";
                    log += timestamp_buf;
                    log += "]";
                    log += " {d} LSUPDATE ";
                    log += c->connection_origin;
                    log += " ";
                    log += to_string(tmp);
                    log +=  " 1 ";
                    log += to_string(check.length());
                    log += " ";
                    log += hexstring_of_unique_obj_id;
                    log += " ";
                    log += origin_start_time;
                    log += " ";
                    log += from;
                    log += "(";
                    log += check;
                    log += ")";
                    log += "\n";
                    write(log_file_dec,log.c_str() ,log.length());
                    fsync(log_file_dec);
                }
                cout << "[" << to_string(c_q->connection_number) << "]";
                cout << " LSUPDATE sent to " << c_q->connection_origin << ", TTL=";
                cout << to_string(tmp) << ", From= " << from ;
                cout << ", MessageID= " << message_id << ", LinkState= ";
                cout << check << "forwards\n";
                write(c_q->socketnumber, temp2.c_str(), temp2.length());
            }
        }
    }
}

static 
string CreateResposneMessage(string src, string sequence)
{
    string to_add = "Traceroute-Response= ";
    to_add += src;
    to_add += " ";
    to_add += sequence;
    return to_add;
}

static
string CreateRequestMessage(string src, string sequence)
{
    string to_add = "Traceroute-Request= ";
    to_add += src;
    to_add += " ";
    to_add += sequence;
    return to_add;
}

static 
string CreateZeroTTLMessage(string src, string sequence)
{
    string to_add = "Traceroute-ZeroTTL= ";
    to_add += src;
    to_add += " ";
    to_add += sequence;
    return to_add;
}


static 
void SendTraceRouteMessage(string flood, string ttl, string destination, string target, string from, string content, bool init)
{
    string traceroute_message = "353NET/1.0 UCASTAPP TRACEROUTE/1.0\r\n";

    traceroute_message += "TTL: ";
    traceroute_message += ttl ;
    traceroute_message += "\r\n";

    traceroute_message += "Flood: 0";
    traceroute_message += "\r\n";

    char node_id[40];
    strcpy (node_id, from.c_str());
    string obj_category = "UCASTAPP";
    char hexstring_of_unique_obj_id[(SHA_DIGEST_LENGTH<<1)+1];
    char origin_start_time[18];
    GetObjID(node_id, obj_category.c_str(), hexstring_of_unique_obj_id, origin_start_time);

    string message_id= hexstring_of_unique_obj_id;
    traceroute_message += "MessageID: ";
    traceroute_message += message_id;
    traceroute_message += "\r\n";

    message_cache.insert(pair<int, string>(message_cache.size(), message_id));

    traceroute_message += "From: ";
    traceroute_message += from;
    traceroute_message += "\r\n";

    traceroute_message += "To: ";
    traceroute_message += destination;
    traceroute_message += "\r\n";

    traceroute_message += "Content-Length: ";
    traceroute_message += to_string(content.length());
    traceroute_message += "\r\n\r\n";

    traceroute_message += content;

    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        shared_ptr<Connection> c = it->second;                         
        if(c->connection_origin == target)
        {
            if(IsLoggingUCASTAPP)
            {
                if(init)
                {
                    char timestamp_buf[32];
                    get_timestamp(timestamp_buf);
                    string log = "[";
                    log += timestamp_buf;
                    log += "]";
                    log += " {i} UCASTAPP ";
                    log += c->connection_origin;
                    log += " ";
                    log += ttl;
                    log += " 0 ";
                    log += to_string(content.length());
                    log += " message_id ";
                    log += from;
                    log += " ";
                    log += destination;
                    log += " ";
                    log += content;
                    log += "\n";
                    write(log_file_dec,log.c_str() ,log.length());
                    fsync(log_file_dec);
                }
                else
                {
                    char timestamp_buf[32];
                    get_timestamp(timestamp_buf);
                    string log = "[";
                    log += timestamp_buf;
                    log += "]";
                    log += " {f} UCASTAPP ";
                    log += c->connection_origin;
                    log += " 0 0 0 ";
                    log += to_string(content.length());
                    log += " message_id ";
                    log += from;
                    log += " ";
                    log += destination;
                    log += " ";
                    log += content;
                    log += "\n";
                    write(log_file_dec,log.c_str() ,log.length());
                    fsync(log_file_dec);
                }
            }
            write(c->socketnumber, traceroute_message.c_str(),traceroute_message.length());
        }
    }
}

static
bool CheckIfNeighborsExist(string parent, string neigh)
{
    for(unsigned int i= 0 ; i < adj_list.size(); i++)
    {
        if(adj_list[i].first == parent)
        {
            bool exist = false;
            for(unsigned int j = 0 ; j < adj_list[i].second.size(); j++)
            {
                if(adj_list[i].second[j]->vertex_cost.first == neigh)
                {
                    exist =true;
                }
            }
            return exist;
        }
    }
    return false;
}

static 
void UpdateNeigborsOfNew(string from, set<string> neighbors)
{
    int temp = -1;
    set<string>OteherNeighs;
    for(unsigned int i = 0 ; i < adj_list.size(); i++)
    {
        if(adj_list[i].first == from)
            temp = i;
        for(unsigned int j = 0 ; j  < adj_list[i].second.size(); j++)
        {
            if(adj_list[i].second[j]->vertex_cost.first == from)
                OteherNeighs.insert(adj_list[i].first);
        }
    }

    for(auto it = OteherNeighs.begin(); it != OteherNeighs.end(); it++)
    {
        string parent = adj_list[temp].first;
        string potential_neighbors = *it;
        if(!CheckIfNeighborsExist(parent, potential_neighbors))
            adj_list[temp].second.push_back(new node(potential_neighbors, 1));
    }

}

static 
void UpdateExisting(string from, set<string> neighbors)
{
    // cout <<"DEBUG UpdateExisting\n";
    for(auto it = neighbors.begin(); it != neighbors.end(); it++)
    {
        for(unsigned int i = 0 ; i < adj_list.size(); i++)
        {
            if(*it == adj_list[i].first)
            {
                bool exist =  false;
                for(unsigned int j = 0 ; j < adj_list[i].second.size(); j++)
                {
                    if(adj_list[i].second[j]->vertex_cost.first == from)
                        exist = true;
                }
                if(!exist)
                    adj_list[i].second.push_back(new node(from, 1));
            }
        }
    }
    // PrintAjdList();
}

// static
// void UpdateExsitingNodeNewNode(string from, set<string> neighbors)
// {
//     for(unsigned int i = 0; i < active_neigh[i].size(); i++)
//     {
//         for(unsigned int j = 0 ; j < adj_list.size(); j++)
//         {
//             if(adj_list[j].first == active_neigh[i] && adj_list[j].first!= master_node_id)
//             {
//                  bool exist = false;
//                  for(unsigned int k = 0 ; k < adj_list[j].second.size(); k++)
//                  {
//                     if( adj_list[j].second[k]->vertex_cost.first == from)
//                         exist = true;
//                  }
//                  if(!exist)
//                     adj_list[j].second.push_back(new node(from,1));   
//             }
//         }
//     }
//     PrintAjdList();
// }

static
void HandleRemoteDisconnect (string from, string parent)
{
    for(unsigned int i = 0 ; i < adj_list.size(); i++)
    {
        if(adj_list[i].first == parent)
        {
            for(unsigned int j = 0 ; j < adj_list[i].second.size(); j++)
            {
                if(adj_list[i].second[j]->vertex_cost.first == from)
                {
                    adj_list[i].second.erase(adj_list[i].second.begin() + j);
                }
            }
        }
    }
    connection_quits = true;
}

static 
void SendDisconnectMessage(string from)
{
    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        shared_ptr<Connection> c_q = it->second;
        string check="";
        string temp2 = "353NET/1.0 LSUPDATE NONE/1.0\r\n";
        temp2 += "TTL: ";
        temp2 += to_string(max_ttl);
        temp2 += "\r\n";
        temp2 += "Flood: 1\r\n";
        temp2 += "MessageID: ";
        char node_id[40];
        strcpy (node_id, from.c_str());
        string obj_category = "LSUPDATE";
        char hexstring_of_unique_obj_id[(SHA_DIGEST_LENGTH<<1)+1];
        char origin_start_time[18];
        GetObjID(node_id, obj_category.c_str(), hexstring_of_unique_obj_id, origin_start_time);
        // string x = from;
        // x += ":";
        // x+= c_q->connection_origin;
        temp2 += hexstring_of_unique_obj_id;
        message_cache.insert(pair<int, string>(message_cache.size(), obj_category));
        temp2 += "\r\n";
        temp2 += "From: ";
        temp2 += from;
        temp2 += "\r\n";
        temp2 += "OriginStartTime: ";
        temp2 += origin_start_time;
        temp2 += "\r\n";
        temp2 += "Content-Length: ";
        temp2 += to_string(check.length());
        temp2 += "\r\n\r\n";
        temp2 += check;
        shared_ptr<string> w = make_shared<string>(temp2);
        if(c_q->state ==1 && c_q->socketnumber >0)
        {
            if(IsLoggingLSUPDATE)
            {
                char timestamp_buf[32];
                get_timestamp(timestamp_buf);
                string log = "[";
                log += timestamp_buf;
                log += "]";
                log += " {i} LSUPDATE ";
                log += c_q->connection_origin;
                log += " ";
                log += to_string(max_ttl);
                log +=  " 1 ";
                log += to_string(check.length());
                log += " ";
                log += hexstring_of_unique_obj_id;
                log += " ";
                log += origin_start_time;
                log += " ";
                log += from;
                log += "(";
                log += check;
                log += ")";
                log += "\n";
                write(log_file_dec,log.c_str() ,log.length());
                fsync(log_file_dec);
            }
            cout << "[" << to_string(c_q->connection_number) << "]";
            cout << " LSUPDATE sent to " <<  c_q->connection_origin << ", TTL=";
            cout << to_string(max_ttl) << ", From= " << from ;
            cout << ", MessageID= " << obj_category << ", LinkState= Disconnect\n";
            write(c_q->socketnumber, temp2.c_str(), temp2.length());
        }
    }
} 

static void SendLSUPDATEfromMaster()
{
    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        shared_ptr<Connection> c_q = it->second;
        string check="";
        string temp2 = "353NET/1.0 LSUPDATE NONE/1.0\r\n";
        temp2 += "TTL: ";
        temp2 += to_string(max_ttl);
        temp2 += "\r\n";
        temp2 += "Flood: 1\r\n";
        temp2 += "MessageID: ";
        char node_id[40];
        strcpy (node_id, master_node_id.c_str());
        string obj_category = "LSUPDATE";
        char hexstring_of_unique_obj_id[(SHA_DIGEST_LENGTH<<1)+1];
        char origin_start_time[18];
        GetObjID(node_id, obj_category.c_str(), hexstring_of_unique_obj_id, origin_start_time);
        // string x = master_node_id;
        // x += ":";
        // x+= c_q->connection_origin;
        temp2 += obj_category;
        message_cache.insert(pair<int,string>(message_cache.size(), obj_category));
        temp2 += "\r\n";
        temp2 += "From: ";
        temp2 += master_node_id;
        temp2 += "\r\n";
        temp2 += "OriginStartTime: ";
        temp2 += origin_start_time;
        temp2 += "\r\n";
        temp2 += "Content-Length: ";
        temp2 += to_string(temp2.length());
        temp2 += "\r\n\r\n";
        for(unsigned int i = 0 ; i < active_neigh.size(); i++)
        {
            check += active_neigh[i];
            check += ",";
        }
        temp2+=check;
        temp2 += "\r\n";
        shared_ptr<string> w = make_shared<string>(temp2);
        if(c_q->state ==1 && c_q->socketnumber >0)
        {
            if(IsLoggingLSUPDATE)
            {
                char timestamp_buf[32];
                get_timestamp(timestamp_buf);
                string log = "[";
                log += timestamp_buf;
                log += "]";
                log += " {i} LSUPDATE ";
                log += c_q->connection_origin;
                log += " ";
                log += to_string(max_ttl);
                log +=  " 1 ";
                log += to_string(check.length());
                log += " ";
                log += hexstring_of_unique_obj_id;
                log += " ";
                log += origin_start_time;
                log += " ";
                log += master_node_id;
                log += "(";
                log += check;
                log += ")";
                log += "\n";
                write(log_file_dec,log.c_str() ,log.length());
                fsync(log_file_dec);
            }
            cout << "[" << to_string(c_q->connection_number) << "]";
            cout << " LSUPDATE sent to " <<  c_q->connection_origin << ", TTL=";
            cout << to_string(max_ttl) << ", From= " << master_node_id ;
            cout << ", MessageID= " << obj_category << ", LinkState= ";
            cout << check << "\n";
            write(c_q->socketnumber, temp2.c_str(), temp2.length());
        }
    }
}


static condition_variable cv_event;
static mutex event_mutex;
static queue<shared_ptr<string > > event_queue;

static
shared_ptr<string> wait_for_event() {
  unique_lock<mutex> l(event_mutex);

  if(!server_state)
    return nullptr;

  while (event_queue.empty()) {
    cv_event.wait(l);
    if(event_queue.size()>0)
        break;
  }
  shared_ptr<string> k = event_queue.front();
  event_queue.pop();
  return k;
}

static 
void add_event(shared_ptr<string> msg) {
    event_mutex.lock();
    event_queue.push(msg);
    cv_event.notify_all();
    event_mutex.unlock();
}

static condition_variable cv;
static mutex work_mutex;
static mutex mutex_m;
static queue<shared_ptr<Connection > > connection_q;

static 
shared_ptr<Connection> wait_for_work() {
  unique_lock<mutex> l(mutex_m);

  if(!server_state)
    return nullptr;

  while (connection_q.empty()) {
    cv.wait(l);
    if(connection_q.size()>0)
        break;
  }
  shared_ptr<Connection> k = connection_q.front();
  connection_q.pop();
  return k;
}


static 
void add_work(shared_ptr<Connection> r) {
    mutex_m.lock();
    connection_q.push(r);
    cv.notify_all();
    mutex_m.unlock();
}

/**
 * Use this code to create a master socket to be used by a server.
 *
 * You should be able to use this function as it.
 *
 * @param port_number_str - port number of the well-known/welcome port.
 * @param debug - non-zero means print to stderr where the server is listening.
 */

// static vector<pair<int,shared_ptr<thread> > > connections;
//key: connection number value: Connection object

static
int create_master_socket(const char *port_number_str, int debug)
{
    int socket_fd = (-1);
    int reuse_addr = 1;
    struct addrinfo hints;
    struct addrinfo* res = NULL;

    signal(SIGPIPE, SIG_IGN);

    memset(&hints,0,sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = 0;
    hints.ai_flags = AI_NUMERICSERV|AI_ADDRCONFIG;

    getaddrinfo("localhost", port_number_str, &hints, &res);
    socket_fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (socket_fd == (-1)) {
        perror("socket() system call");
        exit(-1);
    }
    setsockopt(socket_fd, SOL_SOCKET, SO_REUSEADDR, (void*)(&reuse_addr), sizeof(int));
    bind(socket_fd, res->ai_addr, res->ai_addrlen);
    listen(socket_fd, 2);

    if (debug) {
        struct sockaddr_in server_addr;
        socklen_t server_len = (socklen_t)sizeof(server_addr);

        getsockname(socket_fd, (struct sockaddr *)(&server_addr), &server_len);
        fprintf(stderr,
                "[SERVER] Server listening at %s:%1d\n",
                inet_ntoa(server_addr.sin_addr),
                (int)htons((uint16_t)(server_addr.sin_port & 0x0ffff)));
    }
    return socket_fd;
}


/**
 * Call accept() on the master socket to wait for a client to connect.
 * If no client connects, the function would block indefinitely
 *         (unless an error occurs).
 * If a client connects, this function would create a new socket file descriptor
 *         for communicating with the client.
 *
 * You should be able to use this function as it.
 *
 * @param master_socket_fd - master socket created by create_master_socket().
 * @param debug - non-zero means print to stderr where the client connects from.
 */
static
int my_accept(const int master_socket_fd, int debug)
{
    int newsockfd = (-1);
    struct sockaddr_in cli_addr;
    unsigned int clilen = sizeof(cli_addr);

    newsockfd = accept(master_socket_fd, (struct sockaddr *)(&cli_addr), &clilen);
    if (debug && newsockfd != (-1)) {
        struct sockaddr_in peer;
        socklen_t peer_addr_len = (socklen_t)sizeof(peer);

        getpeername(newsockfd, (struct sockaddr *)(&peer), &peer_addr_len);
        fprintf(stderr,
                "[SERVER] connected to client from %s:%1d\n",
                inet_ntoa(peer.sin_addr),
                (int)htons((uint16_t)(peer.sin_port & 0x0ffff)));
    }
    return newsockfd;
}

static
void usage()
{
    fprintf(stderr, "./echo-server port_number\n");
    exit(-1);
}

/**
 * This is the function you need to change to change the behavior of your server!
 *
 * @param newsockfd - socket that can be used to "talk" (i.e., read/write) to the client.
 */

// int read_a_line(int socket_fd, char *buf, int buf_size)
// {
//     int  bytes_received = read(socket_fd, buf, buf_size);
//     buf[bytes_received] = '\0';
//     return bytes_received;
// }

static int next_connection_number= 1;


static
int create_client_socket(const char *host_name, const char *port_number_str, const int debug)
{
    int socket_fd = (-1);
    struct addrinfo hints;
    struct addrinfo* res = NULL;

    signal(SIGPIPE, SIG_IGN);

    memset(&hints,0,sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = 0;
    hints.ai_flags = AI_NUMERICSERV|AI_ADDRCONFIG;

    getaddrinfo(host_name, port_number_str, &hints, &res);
    socket_fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (socket_fd == (-1)) {
        perror("socket() system call");
        exit(-1);
    }
    if (debug) {
        struct sockaddr_in cs_addr;
        socklen_t cs_len = (socklen_t)sizeof(cs_addr);
        getsockname(socket_fd, (struct sockaddr *)(&cs_addr), &cs_len);
        if((int)htons((uint16_t)(cs_addr.sin_port & 0x0ffff)) != 0)
        {
            fprintf(stderr,
                    "[CLIENT] Client at %s:%1d\n",
                    inet_ntoa(cs_addr.sin_addr),
                    (int)htons((uint16_t)(cs_addr.sin_port & 0x0ffff)));
        }
    }
    return socket_fd;
}

static
int my_connect(const int client_socket_fd, const char *host_name, const char *port_number_str, const int debug)
{
    struct sockaddr_in soc_address;

    memset(&soc_address, 0, sizeof(soc_address));
    if (*host_name >= '0' && *host_name <= '9') {
        soc_address.sin_addr.s_addr = inet_addr(host_name);
    } else {
        struct hostent *p_hostent;

        p_hostent = gethostbyname(host_name);
        memcpy(&soc_address.sin_addr, p_hostent->h_addr, p_hostent->h_length);
    }
    soc_address.sin_family = AF_INET;
    soc_address.sin_port = htons((unsigned short)atoi(port_number_str));

    if (connect(client_socket_fd, (struct sockaddr*)&soc_address, sizeof(soc_address)) == (-1)) {
        return (-1);
    }
    if (debug) {
        struct sockaddr_in cs_addr;
        socklen_t cs_len = (socklen_t)sizeof(cs_addr);

        getpeername(client_socket_fd, (struct sockaddr *)(&cs_addr), &cs_len);
        fprintf(stderr,
                "[CLIENT] Connected to server at %s:%1d\n",
                inet_ntoa(cs_addr.sin_addr),
                (int)htons((uint16_t)(cs_addr.sin_port & 0x0ffff)));
    }
    return 0;
}

static
void connection_reading_thread(int connection_number)
{
    // shared_ptr<Connection> c =nullptr; 
    mutex_m.lock();
    shared_ptr<Connection> c = connection_info[connection_number];
    mutex_m.unlock();

    char m_buf [1024 +1] ="";
    string m = "";
    string from = "";
    int temp = read_a_line(c->socketnumber, m_buf , m);  
    string message= "";
    stringstream ss;
    ss << m;
    ss >> message;
    message= "";
    ss >> message;
    string len = "";
    for(;;)
    {
        string line = "";
        int temp = read_a_line(c->socketnumber, m_buf, line);
        if(line == "\r\n" || line == "\r" || line == "\n")
     
        {
            break;
        }
        string key = ""; string value ="";
        stringstream ss;
        ss << line;
        ss >> key;
        ss >> value;
        if(key == "From:")
            from = value;
        else if(key == "Content-Length:")
            len = value;
    }
    bool dup = false;
    if(c->connection_origin == "unkown")
        c->connection_origin = from;
    if(c->state ==0 && message =="SAYHELLO")
    {
        mutex_m.lock();
        //start-loop
        for(auto it = connection_info.begin(); it != connection_info.end(); it++)
        {
            if(it->first != c->connection_number)
            {
                shared_ptr<Connection> d = it->second;
                if(d->state ==1)
                {
                    for(unsigned int i = 0 ; i < d->neighbor_nodeid.size(); i++)
                    {
                        if(d->neighbor_nodeid[i] == from)
                        {
                            dup = true;
                        }
                    }
                }
            }
        }
        //end-loop
        mutex_m.unlock();
        if(!dup)
        {
            mutex_m.lock();
            c->state = 1;
            c->neighbor_nodeid.push_back(from);
            string ID= from;

            if(IsLoggingSAYHELLO)
            {
                char timestamp_buf[32];
                get_timestamp(timestamp_buf);
                string log = "[";
                log += timestamp_buf;
                log += "] {r} SAYHELLO ";
                log += from;
                log += " 1  0 0 ";
                log += "\n";
                write(log_file_dec,log.c_str() ,log.length());
                fsync(log_file_dec);
            }
            cout << "[" << to_string(c->connection_number) << "]";
            cout << " SAYHELLO message recieved from " << from << endl;
            c->CanLSUpdate = true;
            mutex_m.unlock();

            string temp = "353NET/1.0 SAYHELLO NONE/1.0\r\n";
            temp += "TTL: 1\r\n";
            temp += "Flood: 0\r\n";
            temp += "From: ";
            temp += from;
            temp += "\r\n";
            temp += "Content-Length: 0";
            temp += "\r\n\r\n";
            shared_ptr<string> w = make_shared<string>(temp);
            c->AddWork(w);
            mutex_m.unlock();

            // //write LSUPDATE message
            mutex_m.lock();
            InitialLSUPDATE(from, c);
            active_neigh.push_back(from);
            mutex_m.unlock();
        }
    }
    //sate not 0 || state == 1
    else if(message =="SAYHELLO")
    {
        mutex_m.lock();
        if(IsLoggingSAYHELLO)
        {
            char timestamp_buf[32];
            get_timestamp(timestamp_buf);
            string log = "[";
            log += timestamp_buf;
            log += "] {r} SAYHELLO ";
            log += from;
            log += " 1  0 0 ";
            log += "\n";                
            write(log_file_dec,log.c_str() ,log.length());
            fsync(log_file_dec);
        }
        cout << "[" << to_string(c->connection_number) << "]";
        cout << " SAYHELLO message recieved " << from << endl;
        c->CanLSUpdate = true;
        InitialLSUPDATE(from, c);
        active_neigh.push_back(from);
        mutex_m.unlock();        
    }
    if(!dup)
    {
        bool kill_this_connction = false;
        for(;;)
        {
            string read_ret = "";
            char m_buf [1024 +1] ="";
            string key ="";
            string value ="";
            string message= "";
            string ttl = "";
            string message_id ="";
            string from = "";
            string origin_time = "";
            string len = "";
            string check = "";
            string sequence = "";
            string src ="";
            string flood = "";
            string destination = "";
            set<string> neighbors;
            int counter = 0;
            for(;;)
            {
                ++counter;
                string line = "";
                if (c->socketnumber < 0) {
                    kill_this_connction = true;
                    break;
                }
                int temp =read_a_line(c->socketnumber, m_buf, line);
                // cout << "DEBUG DISCONNECT " << c->socketnumber << " "  << temp << endl;
                if(temp<=0)
                {
                    kill_this_connction = true;
                    cout << "[" << to_string(c->connection_number) << "]";
                    cout << " disconected from ";
                    connection_quits = true;
                    if(c->state!=0)
                    {
                        cout << c->connection_origin <<"> \n";
                        SendDisconnectMessage(c->connection_origin);    
                        for(unsigned int i = 0 ; i < adj_list.size(); i++)
                        {
                            if(adj_list[i].first == master_node_id)
                            {
                                for(unsigned int j = 0 ; j  < adj_list[i].second.size(); j++)
                                {
                                    if(adj_list[i].second[j]->vertex_cost.first == c->connection_origin)
                                        adj_list[i].second.erase(adj_list[i].second.begin()+j);
                                }
                            }
                        }
                        for(unsigned int i = 0 ; i < active_neigh.size(); i++)
                        {
                            if(active_neigh[i] == c->connection_origin)
                                active_neigh.erase(active_neigh.begin()+i);
                        }
                    }
                    else
                        cout <<"\n";
                    break;
                }
                if(line == "\r\n" || line == "\r" || line == "\n")
                {
                    break;
                }
                stringstream ss;
                ss << line;
                string first = "";
                string second = "";
                ss >> first;
                ss >> second;
                if(counter == 1)
                {
                    if (second == "SAYHELLO")
                    {
                        message = second;
                    }
                    else if (second == "UCASTAPP")
                    {
                        message = second;
                    }
                    else if (second == "LSUPDATE")
                    {
                        message = second;
                    }
                }
                else
                {
                    if(first=="TTL:")
                    {
                        ttl = second;
                    }
                    else if(first == "To:")
                    {
                        destination = second;
                    }
                    else if(first == "MessageID:")
                    {
                        message_id = second;
                    }
                    else if(first == "From:")
                    {
                        from = second;
                    }
                    else if(first == "OriginStartTime:")
                    {
                        origin_time = second;
                    }
                    else if(first== "Flood:")
                    {
                        flood = second;
                    }
                    else if(first == "Content-Length:")
                    {
                        len = second;
                    }
                    if(!server_state)
                    {
                        mutex_m.unlock();
                        break;
                    }
                }
            }       


            if(kill_this_connction)
                break;

            int length = 0;

            if(len.length()>0)
            {
                length = stoi(len);
            }
            
            if(length>0)
            {
                int bytes_read =read(c->socketnumber, m_buf , length);
                if(bytes_read <=0 )
                    break;
                m_buf[bytes_read] = '\0';
            }

            mutex_m.lock();
            if(message== "SAYHELLO")
            {
                if(IsLoggingSAYHELLO)
                {
                    char timestamp_buf[32];
                    get_timestamp(timestamp_buf);
                    string log = "[";
                    log += timestamp_buf;
                    log += "] {r} SAYHELLO ";
                    log += from;
                    log += " 1  0 0 ";
                    log += "\n";
                    write(log_file_dec,log.c_str() ,log.length());
                    fsync(log_file_dec);
                }
                cout << "[" << to_string(c->connection_number) << "]";
                cout << " SAYHELLO message recieved from " << from << endl;
                c->CanLSUpdate = true;

                string temp = "353NET/1.0 SAYHELLO NONE/1.0\r\n";
                temp += "TTL: 1\r\n";
                temp += "Flood 0\r\n";
                temp += "From: ";
                temp += from;
                temp += "\r\n";
                temp += "Content-Length: 0";
                temp += "\r\n\r\n";
                shared_ptr<string> w = make_shared<string>(temp);
                c->AddWork(w);
            }
            else if(message == "UCASTAPP")
            {
                stringstream ss;
                ss << m_buf;
                string message_type = ""; 
                string src = "";
                string sequence= "";
                ss >> message_type;
                ss >> src;
                ss >> sequence;
                if(message_type == "Traceroute-Request=")
                {
                    if(master_node_id == destination)
                    {
                        string target = GetTarget(from);
                        string resposne = CreateResposneMessage(master_node_id, sequence);
                        SendTraceRouteMessage(flood, "0", from, target, destination, resposne, false);
                    }
                    else
                    {
                        int check_ttl = stoi(ttl);
                        --check_ttl;
                        if(check_ttl ==0)
                        {
                            string send_back = CreateZeroTTLMessage(master_node_id, sequence);
                            string target = GetTarget(from);
                            SendTraceRouteMessage(flood, "0" , from, target, master_node_id, send_back, false);
                        }
                        else
                        {
                            string forward = CreateRequestMessage(src, sequence);
                            string target = GetTarget(destination);
                            SendTraceRouteMessage(flood, to_string(check_ttl) , destination, target, from, forward, false);
                        }
                    }
                }
                else if (message_type == "Traceroute-Response=")
                {
                    if(destination ==master_node_id)
                    {
                        string send_back = CreateResposneMessage(src, sequence);
                        send_back += " ";
                        send_back += message_id;
                        shared_ptr<string> w = make_shared<string>(send_back);
                        string for_content = *w;
                        if(IsLoggingUCASTAPP)
                        {
                            char timestamp_buf[32];
                            get_timestamp(timestamp_buf);
                            string log = "[";
                            log += timestamp_buf;
                            log += "]";
                            log += " {i} UCASTAPP ";
                            log += destination;
                            log += " 0 0 0 ";
                            log += to_string(for_content.length());
                            log += " message_id ";
                            log += master_node_id;
                            log += " ";
                            log += destination;
                            log += " ";
                            log += for_content;
                            log += "\n";
                            write(log_file_dec,log.c_str() ,log.length());
                            fsync(log_file_dec);
                        }
                        add_event(w);
                    }
                    else
                    {
                        string send_back = CreateResposneMessage(src, sequence);
                        string target = GetTarget(destination);
                        SendTraceRouteMessage(flood, ttl , destination, target, from, send_back, false);
                    }
                }
                else if (message_type == "Traceroute-ZeroTTL=")
                {
                    if(destination ==master_node_id)
                    {
                        string send_back = CreateZeroTTLMessage(src, sequence);
                        send_back += " ";
                        send_back += message_id;
                        shared_ptr<string> w = make_shared<string>(send_back); 
                        string for_content = *w;
                        if(IsLoggingUCASTAPP)
                        {
                            char timestamp_buf[32];
                            get_timestamp(timestamp_buf);
                            string log = "[";
                            log += timestamp_buf;
                            log += "]";
                            log += " {i} UCASTAPP ";
                            log += destination;
                            log += " 0 0 0 ";
                            log += to_string(for_content.length());
                            log += " message_id ";
                            log += master_node_id;
                            log += " ";
                            log += destination;
                            log += " ";
                            log += for_content;
                            log += "\n";
                            write(log_file_dec,log.c_str() ,log.length());
                            fsync(log_file_dec);
                        }
                        add_event(w);
                    }
                    else
                    {
                        string send_back = CreateZeroTTLMessage(src, sequence);
                        string target = GetTarget(destination); 
                        SendTraceRouteMessage(flood, ttl , destination, target, from, send_back, false);
                    }  
                }
                else
                {
                    cout << "UNREADABLE CONTENT\n";
                }
            }
            else if(message == "LSUPDATE")
            {
                stringstream ss;
                ss << m_buf;
                while(ss)
                {
                    string t;
                    ss >> t;
                    if(t.size()>0)
                    {
                        string query="";
                        for(unsigned int i = 0 ; i < t.length(); i++)
                        {
                            if(t[i]==',')
                            {
                                neighbors.insert(query);
                                query ="";
                            }
                            else
                                query += t[i];
                        }
                    }
                }

                bool newNode = true;
                for(unsigned int j = 0 ; j < adj_list.size(); j++)
                {
                    if(adj_list[j].first == from)
                        newNode =false;
                }

                string log_check = "";                
                for(auto it = neighbors.begin(); it!= neighbors.end(); it++)
                {
                    log_check += *it;
                    log_check  += ", ";
                }

                if(IsLoggingLSUPDATE)
                {
                    char timestamp_buf[32];
                    get_timestamp(timestamp_buf);
                    string log = "[";
                    log += timestamp_buf;
                    log += "]";
                    log += " {r} LSUPDATE ";
                    log += c->connection_origin;
                    log += " ";
                    log += ttl;
                    log +=  " 1 ";
                    log += to_string(log_check.length());
                    log += " ";
                    log += message_id;
                    log += " ";
                    log += origin_time;
                    log += " ";
                    log += from;
                    log += "(";
                    log += log_check;
                    log += ")";
                    log += "\n";
                    write(log_file_dec,log.c_str() ,log.length());
                    fsync(log_file_dec);
                }

                cout << "[" << to_string(c->connection_number) << "]";
                cout << "LSUPDATE recieved from " << c->connection_origin;
                cout << ", TTL= " << ttl << " From=" << from;
                cout << ", message_id " << message_id << ", LinkState=";

                for(auto it = neighbors.begin(); it!= neighbors.end(); it++)
                    cout << *it << ",";
                cout << ".Constant reading";
                cout << endl;

                // cout << "DEBUG List before update\n";
                // PrintAjdList();

                if(from == master_node_id)
                {
                    InitialLSUPDATE(from, c);
                    newNode =false;
                }
                //flood the entire network
                if(newNode)
                {
                    vector<node*> n;
                    for(auto it = neighbors.begin(); it!= neighbors.end() ; it++)
                    {
                        n.push_back(new node(*it, 1));
                    }
                    adj_list.push_back(make_pair(from, n));
                    bool flood = true;
                    for(unsigned int j = 0 ; j < active_neigh.size(); j++)
                    {
                        if(from == active_neigh[j])
                        {
                            flood = false;
                        }
                    }
                    // cout << "DEBUG FLOOD\n";
                    // cout << flood << endl;
                    if(flood)
                    {
                        // adj_list.push_back(make_pair(from, n)); 
                        SendLSUPDATEfromMaster();
                    }
                }
                UpdateNeigborsOfNew(from, neighbors);
                UpdateExisting(from, neighbors);

                int tmp = stoi(ttl);
                --tmp;
                //forwarding message
                if(tmp != 0)
                {
                    // cout << "FOWARDING ATTEMPTED\n";
                    floodLSUDPATEMessage(tmp , from ,message_id, neighbors, c);
                }
                if(neighbors.size() == 0)
                {
                    HandleRemoteDisconnect(from, c->connection_origin);
                }
            }
            // end-if lab 12 unlock
            mutex_m.unlock();
        }
        // mutex_m.unlock();
    }
    c->AddWork(NULL);
    mutex_m.lock();
    if(c->socketnumber >= 0 )
    {
        shutdown(c->socketnumber, SHUT_RDWR);
        close(c->socketnumber);
    }
    c->socketnumber = -2;       
    mutex_m.unlock();
    add_work(c);
}

static
void connection_writing_thread(int connection_number)
{
    mutex_m.lock();
    shared_ptr<Connection> c = connection_info[connection_number];
    mutex_m.unlock();
    if(!c || c->socketnumber <0)
        return;
    for(;;)
    {
        shared_ptr<string > w  = c->WaitForWork();
        if(!w)
        {
            break;
        }
        string temp = *w;
        stringstream ss;
        ss << temp;
        string first = "";
        string second = "";
        ss >> first;
        ss >> second;
        if(second =="SAYHELLO")
        {
            mutex_m.lock();
            if(IsLoggingSAYHELLO)
            {
                char timestamp_buf[32];
                get_timestamp(timestamp_buf);
                string log = "[";
                log += timestamp_buf;
                log += "] {i} SAYHELLO ";
                log += master_node_id;
                log += " 1  0 0 ";
                log += "\n";
                write(log_file_dec,log.c_str() ,log.length());
                fsync(log_file_dec);
            }
            string temp = "353NET/1.0 SAYHELLO NONE/1.0\r\n";
            temp += "TTL: 1\r\n";
            temp += "Flood: 0\r\n";
            temp+= "From: ";
            temp += master_node_id;
            temp += "\r\n";
            temp += "Content-Length: 0";
            temp += "\r\n\r\n";
            write(c->socketnumber, temp.c_str(), temp.length());
            mutex_m.unlock();
        }
        else if(second =="LSUPDATE")
        {
            mutex_m.lock();
            string ttl = "";
            string message_id ="";
            string from = "";
         
            string origin_time = "";
            string len = "";
            bool IsBuildList =false;
            bool newNode = true;
            set<string> neighbors;
            while(ss)
            {
                string t;
                ss >> t;
                if(t == "LSUPDATE")
                {
                    neighbors.clear();
                    IsBuildList = false;
                }
                else if(t=="TTL:")
                {
                    IsBuildList = false;                    
                    ss >> ttl;
                }
                else if(t == "MessageID:")
                {
                    IsBuildList = false;                    
                    ss >> message_id;
                }
                else if(t == "From:")
                {
                    IsBuildList = false;
                    ss >> from;
                }
                else if(t == "OriginStartTime:")
                {
                    IsBuildList = false;
                    ss >> origin_time;
                }
                else if(t == "Content-Length:")
                {
                    ss >> len;
                    IsBuildList = true;
                    neighbors.clear();
                }
                else if(IsBuildList)
                {
                    if(t.size()>0)
                    {
                        string query="";
                        for(unsigned int i = 0 ; i < t.length(); i++)
                        {
                            if(t[i]==',')
                            {
                                neighbors.insert(query);
                                query ="";
                            }
                            else
                                query += t[i];
                        }
                    }
                }
            }

            string log_check = "";                
            for(auto it = neighbors.begin(); it!= neighbors.end(); it++)
            {
                log_check += *it;
                log_check += ", ";
            }

            if(IsLoggingLSUPDATE)
            {
                char timestamp_buf[32];
                get_timestamp(timestamp_buf);
                string log = "[";
                log += timestamp_buf;
                log += "]";
                log += " {r} LSUPDATE ";
                log += c->connection_origin;
                log += " ";
                log += ttl;
                log +=  " 1 ";
                log += to_string(log_check.length());
                log += " ";
                log += message_id;
                log += " ";
                log += origin_time;
                log += " ";
                log += from;
                log += "(";
                log += log_check;
                log += ")";
                log += "\n";
                write(log_file_dec,log.c_str() ,log.length());
                fsync(log_file_dec);
            }

            cout << "[" << to_string(c->connection_number) << "]";
            cout << "LSUPDATE recieved from " << c->connection_origin;
            cout << ", TTL= " << ttl << " From=" << from;
            cout << ", message_id " << message_id << ", LinkState=";

            for(auto it = neighbors.begin(); it!= neighbors.end(); it++)
                cout << *it << ",";
            cout << ". WaitForWork "<< endl;
            
            for(unsigned int j = 0 ; j < adj_list.size(); j++)
            {
                if(adj_list[j].first == from)
                    newNode =false;
            }
       
            // cout << "DEBUG List before update\n";
            // PrintAjdList();
   
            if(newNode)
            {

                bool flood = true;
                vector<node*> n;
                for(auto it = neighbors.begin(); it!= neighbors.end() ; it++)
                {
                    n.push_back(new node(*it, 1));
                }
                adj_list.push_back(make_pair(from, n));
                for(unsigned int j = 0 ; j < active_neigh.size(); j++)
                {
                    if(from == active_neigh[j])
                    {
                        flood = false;
                    }
                }
                // cout << "DEBUG FLOOD\n";
                // cout << flood << endl;
                if(flood)
                {
                    SendLSUPDATEfromMaster();
                }
            }
            UpdateNeigborsOfNew(from ,neighbors);
            UpdateExisting(from, neighbors);  

            int tmp = stoi(ttl);
            --tmp;
            string to ="";
            //this is not a new node you gotta decrement ttl and flood
            if(tmp != 0)
            {
                // cout << "FOWARDING ATTEMPTED\n";
                floodLSUDPATEMessage(tmp , from ,message_id, neighbors, c);
            }
            if(neighbors.size()==0)
            {
                HandleRemoteDisconnect(from, c->connection_origin);
            }
            mutex_m.unlock();
        }
    mutex_m.unlock();
    }
}

static
void timer_thread(int *param)
{
    int counter  =0;
    for(;;)
    {
        usleep(1000000);
        if(*param == (-1))
        {
            break;
        }     
        counter++; 
        if(counter == msg_lifetime)
        {
            add_event(NULL);
        }  
    }
}

static
void timestamp_diff(struct timeval *t1, struct timeval *t2, struct timeval *t2_minus_t1)
    /* only works if t2 comes after t1 */
{
    if (t2->tv_usec >= t1->tv_usec) {
        /* no need to borrow */
        t2_minus_t1->tv_usec = t2->tv_usec - t1->tv_usec;
        t2_minus_t1->tv_sec = t2->tv_sec - t1->tv_sec;
    } else {
        /* borrow 1 second as 1000000 microseconds */
        t2_minus_t1->tv_usec = 1000000 + t2->tv_usec - t1->tv_usec;
        t2_minus_t1->tv_sec = t2->tv_sec - 1 - t1->tv_sec;
    }
}

static
void format_event_time(struct timeval *now, char *buf, int buf_sz)
{
    struct timeval event_time;

    timestamp_diff(&start_time, now, &event_time);
    snprintf(buf, buf_sz, "%010d.%010d", (int)(event_time.tv_sec), (int)(event_time.tv_usec));
}

static
void console_terminal(int master_socket_fd)
{
    string command;
	while(true)
	{
		cout << master_node_id << "> \n";
        getline(cin, command);
        stringstream ss;
        ss << command;
        string first_command="";
        string second_command="";
        bool first =1;
        while(ss)
        {
            if(first)
            {
                ss >>first_command;
                first=!first;
            }
            else
                ss>> second_command;
        }
		if(first_command== "help")
        {
            mutex_m.lock();
            cout << "Available commands are:\n\thelp\n\tkill #\n\tquit\n\tstatus\n\tstatus #\n" ;
            mutex_m.unlock();
        }
		else if (first_command == "neighbors")
        {
            mutex_m.lock();
            cout << "Neighbors of " << master_node_id << ":\n";
            for(unsigned int i = 0 ; i < active_neigh.size(); i++)
            {
                cout << "\t" << active_neigh[i] << "\n";
            }
            cout << endl;
            mutex_m.unlock();
        }
        else if(first_command =="forwarding")
        {
            mutex_m.lock();
            forwarding(true);
            mutex_m.unlock();
        }
        else if(first_command =="netgraph")
        {
            //Run Dijkstra here start at master_node
            mutex_m.lock();
            vector<pair<string, vector<node*> > > res; 
            if(adj_list.size()==0)
            {
                cout << master_node_id << " has no neighbors\n";
            }
            else
            {
                if(connection_quits)
                {
                    set<node*> ret_forward;
                    ret_forward = BFS(new node(master_node_id, 1));
                    set<string> ret;
                    for(auto it = ret_forward.begin(); it!= ret_forward.end(); it++)
                    {
                        node* temp = *it;
                        ret.insert(temp->vertex_cost.first);
                    }
                    for(unsigned int i = 0 ; i < adj_list.size(); i++)
                    {
                        bool exist = false;
                        for(auto it = ret.begin(); it != ret.end(); it++)
                        {
                            if(adj_list[i].first == *it)
                                exist =true;
                        }
                        if(exist)
                        {
                            res.push_back(adj_list[i]);
                        }
                    }
                    adj_list.clear();
                    for(unsigned int i = 0 ; i < res.size(); i++)
                        adj_list.push_back(res[i]);
                    connection_quits = false;
                }
                PrintAjdList();
            }
            mutex_m.unlock();
        }
        else if(first_command== "quit")
		{
            mutex_m.lock();
            server_state=false;
            for(auto it = connection_info.begin(); it!= connection_info.end(); it++)
            {
                if(it->second->socketnumber >=0 && it->second->connection_number == master_connection)
                {
                    shared_ptr<Connection> c = it->second; 
                    c->AddWork(NULL);
                    shutdown(c->socketnumber, SHUT_RDWR);
                    close(c->socketnumber);
                    c->socketnumber =-1;
                }
            }
            shutdown(master_socket_fd, SHUT_RDWR);
            close(master_socket_fd);
            mutex_m.unlock();
            add_work(nullptr);
            break;
		}
        else if(first_command== "traceroute")
        {
            if(second_command.length()==0)
                cout << "Invalid operation\n";
            else
            {
                vector<node*> ret = forwarding(false);
                string destination = second_command;
                string target = GetTarget(destination);
                for(int i = 1 ; i < max_ttl ; i++)
                {
                    struct timeval start_time;
                    gettimeofday(&start_time , NULL);
                    string content = CreateRequestMessage(master_node_id, to_string(i));
                    SendTraceRouteMessage(to_string(i) , to_string(i), destination, target, master_node_id, content, true);
                    int indicator = 0;
                    shared_ptr<thread> timer = make_shared<thread>(timer_thread, &indicator);
                    shared_ptr<string> resposne = wait_for_event();

                    string message_type = "";
                    string node_id = "";
                    string sequence_number = "";
                    string message_id = "";
                    string for_content = "";
                    if(resposne)
                    {
                        for_content = *resposne;
                        indicator = -1;
                        stringstream ss;
                        ss << *resposne;
                        ss >> message_type;
                        ss >> node_id;
                        ss >> sequence_number;
                        ss >> message_id;
                    }

                    if(!resposne)
                    {
                        indicator = -1;
                        cout << to_string(i) << " - Timeout occurred, target not reached\n"; 
                        timer->join();
                        break;
                    }
                    else if (message_type == "Traceroute-ZeroTTL=")
                    {
                        if(IsLoggingUCASTAPP)
                        {
                            char timestamp_buf[32];
                            get_timestamp(timestamp_buf);
                            string log = "[";
                            log += timestamp_buf;
                            log += "]";
                            log += " {r} UCASTAPP ";
                            log += master_node_id;
                            log += " 0 0 0 ";
                            log += to_string(for_content.length());
                            log += message_id;
                            log += " ";
                            log += node_id;
                            log += " ";
                            log += destination;
                            log += " ";
                            log += for_content;
                            log += "\n";                            
                            write(log_file_dec,log.c_str() ,log.length());
                            fsync(log_file_dec);
                        }
                        struct timeval now;
                        gettimeofday(&now , NULL);
                        struct timeval diff;
                        timestamp_diff(&start_time, &now, &diff);
                        char m_buf[1024];
                        format_event_time(&diff, m_buf , sizeof(m_buf));
                        cout << sequence_number << " - " << node_id << ", " << m_buf << "\n";
                    }
                    else if (message_type == "Traceroute-Response=")
                    {
                        if(IsLoggingUCASTAPP)
                        {
                            char timestamp_buf[32];
                            get_timestamp(timestamp_buf);
                            string log = "[";
                            log += timestamp_buf;
                            log += "]";
                            log += " {r} UCASTAPP ";
                            log += node_id;
                            log += " 0 0 0 ";
                            log += to_string(for_content.length());
                            log += message_id;
                            log += " ";
                            log += node_id;
                            log += " ";
                            log += destination;
                            log += " ";
                            log += for_content;
                            log += "\n";
                            write(log_file_dec,log.c_str() ,log.length());
                            fsync(log_file_dec);
                        }
                        struct timeval now;
                        gettimeofday(&now , NULL);
                        struct timeval diff;
                        timestamp_diff(&start_time, &now, &diff);
                        char m_buf[1024];
                        format_event_time(&diff, m_buf , sizeof(m_buf));
                        cout << to_string(i) << " - " << node_id << ", " << m_buf << "\n";
                        timer->join();
                        break;
                    }
                    timer->join();  
                }
            }
        }
        else if(first_command== "status")
		{
            mutex_m.lock();
            if(second_command.length()>0)
            {
                bool found =false;
                stringstream ss;
                ss << second_command;
                int con_number;
                ss >> con_number;
                for(auto it = connection_info.begin(); it != connection_info.end() ; it++)
                {
                    if(it->first == con_number)
                        found = true;
                }

                if(!found)
                    cout << "Invalid connection number: " << second_command << "\n";
                else
                {
                    cout << "[" << second_command << "]\tSocket: "<< connection_info[con_number]->socketnumber << "\n\tstate: " << to_string(connection_info[con_number]->state) << "\n";
                    cout << "\tNeighbors : ";
                    for(unsigned int i = 0 ; i < connection_info[con_number]->neighbor_nodeid.size(); i++)
                    {
                        // if(connection_info[con_number]->neighbor_nodeid[i]!= "unkown")
                            cout << connection_info[con_number]->neighbor_nodeid[i]  << " ";
                    }
                    cout << endl;
                    cout << "\torigin_node: " << connection_info[con_number]->connection_origin << endl;
                }
            }
            else
            {
                if(connection_info.size()>0)
                {
                    cout << "The following connections are active: ";
                    for(auto it= connection_info.begin(); it != connection_info.end(); it++)
                        cout << it->first <<" ";
                    cout << endl;
                    for(auto it= connection_info.begin(); it != connection_info.end(); it++)
                    {
                        cout << "[" << it->first << "]\tSocket: "<< connection_info[it->first]->socketnumber << "\n\tstate: " << to_string(connection_info[it->first]->state) << "\n";
                        cout << "\tNeighbors : ";
                        for(unsigned int i = 0 ; i < connection_info[it->first]->neighbor_nodeid.size(); i++)
                            cout << connection_info[it->first]->neighbor_nodeid[i]  << " ";
                        cout << endl;
                    }
                    cout << endl;
                }
                else
                    cout << "No active connections.\n";
            }
            mutex_m.unlock();
		}
        else
        {
            mutex_m.lock();
            cout << "command not recognized. Valid commands are:\n";
            cout << "\tfrowarding\n";
            cout << "\tneighbors\n";
            cout << "\tnetgraph\n";
            cout << "\ttraceroute target\n";
            cout << "\tquit\n";
            mutex_m.unlock();
        }
	}
}

void reaper()
{
    for(;;)
    {
        shared_ptr<Connection> c = wait_for_work();
        if(!c)
        {
            break;
        }
        c->read_thread->join();
        c->write_thread->join();
        vector<pair<shared_ptr<thread>, int > > temp;
        mutex_m.lock();
        connection_info.erase(c->connection_number);
        if(server_state)
        {
            connection_info.erase(c->connection_number);
        }
        else
        {
            connection_info.erase(c->connection_number);
            mutex_m.unlock();
            while(!connection_q.empty())
            {
                shared_ptr<Connection> temp_c = connection_q.front();
                connection_q.pop();
                temp_c->write_thread->join();
                temp_c->read_thread->join();
            }
            break;
        }
        mutex_m.unlock();
    }

    mutex_m.lock();
    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        if(it->second->socketnumber >=0)
        {
            shutdown(it->second->socketnumber, SHUT_RDWR);
            close(it->second->socketnumber);
            it->second->socketnumber = -1;
        }
    }
    mutex_m.unlock();


    for(auto it = connection_info.begin(); it != connection_info.end(); it++)
    {
        it->second->write_thread->join();
        it->second->read_thread->join();
    }
    mutex_m.lock();
    connection_info.clear();
    mutex_m.unlock();
}

static 
vector<map<string, map<string, string> > > parse_config_file(char* file_name)
{
    vector<map<string, map<string, string> > > ret;
    ifstream file(file_name);
    if(!file.good())
        return ret; 
    std::string line;
    stringstream ss;
    while(getline(file, line))
    {
        ss << line;
        ss <<" ";
    }
    string sec_query;
    while(ss)
    {
        string temp;
        ss>> temp;
        if(temp[0] == '[')
        {
            string res;
            for(unsigned int i =1 ; i < temp.length(); i++)
            {
                if(temp[i]!=']')
                    res += temp[i];
            }
            sec_query = res;
            map<string, map<string, string> > s;
            map<string, string> t;
            s.insert(make_pair(res, t));
            ret.push_back(s);
        }
        else
        {
            if(temp[0]!=';' && temp.length()!=0)
            {
                string key, value;
                bool isKey=true;
                for(unsigned int i = 0 ; i < temp.length(); i++)
                {
                    
                    if(temp[i] =='=')
                        isKey=false;
                    else if(isKey)
                        key += temp[i];
                    else
                        value += temp[i];
                }
                map<string, string> s;
                s.insert(make_pair(key,value));
                ret[ret.size()-1][sec_query].insert(make_pair(key, value));
            }
        }
    }
    return ret; 
}

static
void neighbor(map<string, string> temp_neigh)
{
    vector<pair<string, vector<string>  > > list_of_neighbor;
    for(auto it = temp_neigh.begin() ; it != temp_neigh.end(); it++)
    {
        string node = it->first;
        string neigh = it->second;
        vector<string> temp;
        string x = "";
        for(unsigned int i = 0 ; i < neigh.length(); i++)
        {
            if(neigh[i]==',')
            {
                if(x != master_node_id)
                temp.push_back(x);
                x="";
            }
            else if(i == neigh.length()-1)
            {
                x+= neigh[i];
                temp.push_back(x);
                x="";
            }
            else
                x+= neigh[i];
        }
        list_of_neighbor.push_back(make_pair(node, temp));
    }
    for(;;)
    {
        vector<string> l;
        for(unsigned int i =0 ; i < list_of_neighbor.size(); i++)
        {
            if(list_of_neighbor[i].first == master_node_id)
            {
                for(unsigned int j =0 ; j < list_of_neighbor[i].second.size(); j++)
                    l.push_back(list_of_neighbor[i].second[j]);
            }
        }
        mutex_m.lock();
        if(server_state)
        {
            for(auto it = connection_info.begin(); it != connection_info.end(); it++)
            {
                shared_ptr<Connection> c = it->second;
                if(c)
                {
                    for(unsigned int i = 0 ;i < l.size(); i++)
                    {
                        for(unsigned int j = 0 ;j < c->neighbor_nodeid.size(); j++)
                        {
                            if(c->connection_origin == "unkown")
                                c->connection_origin = c->neighbor_nodeid[j]; 
                            if(l[i] == c->neighbor_nodeid[j])
                                l.erase(l.begin() +i);
                        }
                    }
                }
            }
        }   
        else
        {
            mutex_m.unlock();
            break;
        }
        mutex_m.unlock();

        for(unsigned int i = 0; i < l.size(); i++)
        {
            string query = l[i];
            string port=""; string host ="";
            bool change = false;
            for(unsigned int j =0 ; j < query.length(); j++)
            {
                if(query[j] == ':')
                    change = true;
                else if(change)
                    port+= query[j];
                else if(!change)
                    host+=query[j];
            }
            int socket = create_client_socket(master_host.c_str(),master_port.c_str(),1);
            if(socket<0)
            {
                cout << "neighbor error\n";
                return;
            }
            int x= my_connect(socket, host.c_str(), port.c_str(), 1);
            if(x >= 0 )
            {
                mutex_m.lock();
                // Connection* c = new Connection(socket, next_connection_number);
                shared_ptr<Connection> c = make_shared<Connection>(socket, next_connection_number);
                ++next_connection_number;
                shared_ptr<thread> r_thr = make_shared<thread>(connection_reading_thread, c->connection_number);
                shared_ptr<thread> w_thr = make_shared<thread>(connection_writing_thread, c->connection_number);
                c->SetThread(r_thr, w_thr);
                c->state = 1;
                string t = host;
                t+=":";
                t+= port;
                c->connection_origin = t;
                c->neighbor_nodeid.push_back(t);
                connection_info.insert(make_pair(c->connection_number, c));
                if(IsLoggingSAYHELLO)
                {
                    char timestamp_buf[32];
                    get_timestamp(timestamp_buf);
                    string log = "[";
                    log += timestamp_buf;
                    log += "] {i} SAYHELLO ";
                    log += master_node_id;
                    log += " 1  0 0 ";
                    log += "\n";
                    write(log_file_dec,log.c_str() ,log.length());
                    fsync(log_file_dec);
                }
                string temp = "353NET/1.0 SAYHELLO NONE/1.0\r\nFrom: ";
                temp += t;
                temp += "\r\nContent-Length: 0";
                temp += "\r\n\r\n";
                shared_ptr<string> w = make_shared<string>(temp);
                c->AddWork(w);
                mutex_m.unlock();
            }
        }
        mutex_m.unlock();
        usleep(sleep_time_neigh * 1000000);
    }
}


int main(int argc, char *argv[])
{
    int master_socket_fd = (-1);
    if (argc != 2) {
        usage();
    }

    config = parse_config_file(argv[1]);

        //cofig file parsed
    map<string, map<string, string> >::iterator it_server = config[0].begin();
    
    //server conifg
    string host = config[0][it_server->first]["host"];
    string port_number = config[0][it_server->first]["port"];
    string pidfile = config[0][it_server->first]["pidfile"];
    string logfile = config[0][it_server->first]["logfile"];

    master_node_id = host;
    master_node_id+=":";
    master_node_id+=port_number;

    master_host = host;
    master_port = port_number;

    it_server = config[1].begin();
    map<string, string> temp_neigh = config[1][it_server->first];

    it_server = config[3].begin();
    sleep_time_neigh = stoi(config[3][it_server->first]["neighbor_retry_interval"]);
    max_ttl = stoi(config[3][it_server->first]["max_ttl"]);
    msg_lifetime = stoi(config[3][it_server->first]["msg_lifetime"]);

    it_server = config[4].begin();
    string SAYHELLO_logging = config[4][it_server->first]["SAYHELLO"];
    string LSUPDATE_logging = config[4][it_server->first]["LSUPDATE"];
    string UCASTAPP_logging = config[4][it_server->first]["UCASTAPP"];

    if(SAYHELLO_logging == "1")
        IsLoggingSAYHELLO = true;
    else if (SAYHELLO_logging == "0") 
        IsLoggingSAYHELLO = false;

    if(LSUPDATE_logging == "1")
        IsLoggingLSUPDATE = true;
    else if(LSUPDATE_logging== "0")
        IsLoggingLSUPDATE =false;

    if(UCASTAPP_logging =="1")
        IsLoggingUCASTAPP = true;
    else if (UCASTAPP_logging == "0")
        IsLoggingUCASTAPP = false;

    server_state = true;
    master_socket_fd = create_master_socket(port_number.c_str() , 1);
    thread command_promt_thread = thread(console_terminal, master_socket_fd);
    thread reaper_thread = thread(reaper);
    thread neighbor_thread = thread(neighbor, temp_neigh);

    mutex_m.lock();
    //PID file writing
    int pid = (int) getpid();
    string pid_s = to_string(pid);
    pid_s+="\n";
    int pid_dec = open(pidfile.c_str(), O_RDONLY);
    if(pid_dec == (-1))
        pid_dec = open(pidfile.c_str(), O_WRONLY|O_CREAT, 0600);
    else
    {
        close(pid_dec);
        pid_dec = open(pidfile.c_str(), O_WRONLY|O_TRUNC);
    }
    write(pid_dec, pid_s.c_str(),pid_s.length());
    fsync(pid_dec);
    close(pid_dec);
    mutex_m.unlock();

    mutex_m.lock();
    //Open log file
    log_file_dec =open(logfile.c_str(), O_RDONLY);
    if(log_file_dec==(-1))
        log_file_dec = open(logfile.c_str(), O_WRONLY|O_CREAT, 0600);
    else
    {
        close(log_file_dec);
        log_file_dec = open(logfile.c_str(), O_WRONLY|O_APPEND);   
    }
    char timestamp_buf[32];
    get_timestamp(timestamp_buf);
    string start_server_message="Server started at [";
    start_server_message+= timestamp_buf;
    start_server_message+= "]\nServer listening on port ";
    start_server_message+= port_number;
    start_server_message += "\n";
    write(log_file_dec,start_server_message.c_str() ,start_server_message.length());
    fsync(log_file_dec);
    mutex_m.unlock();


    for (;;) {
        int newsockfd = (-1);
        newsockfd = my_accept(master_socket_fd, 1);
        if(newsockfd ==(-1))break;
        mutex_m.lock();
        if(!server_state)
        {
            shutdown(newsockfd, SHUT_RDWR);
            close(newsockfd);
            mutex_m.unlock();
            break;
        }
        shared_ptr<Connection> new_connection = make_shared<Connection>(newsockfd, next_connection_number);
        next_connection_number++;
        master_connection = new_connection->connection_number;
        new_connection->state = 0;
        shared_ptr<thread> r_thr = make_shared<thread>(connection_reading_thread, new_connection->connection_number);
        shared_ptr<thread> w_thr = make_shared<thread>(connection_writing_thread, new_connection->connection_number);
        new_connection->SetThread(r_thr, w_thr);
        new_connection->neighbor_nodeid.push_back("unkown");
        new_connection->connection_origin = "unkown";
        connection_info.insert(make_pair(new_connection->connection_number, new_connection));
        mutex_m.unlock();
    }
    command_promt_thread.join();
    reaper_thread.join();
    neighbor_thread.join();
    connection_info.clear();
    return 0;
}