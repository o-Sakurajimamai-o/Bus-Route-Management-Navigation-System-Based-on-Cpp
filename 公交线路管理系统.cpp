// 公交线路管理: 2023-11-12

/**********************说明*****************************
 * 版权所有 (C)2023, 王浩然
 *
 * 文件名称： 交通管理查询系统.cpp
 * 文件标识：无
 * 内容摘要：实现公交管理功能
 * 其它说明：无
 * 当前版本： V1.0
 * 作   者：王浩然
 * 完成日期： 20231112
 *
 * 修改记录1：
 * 修改日期： 20231112
 * 版本号： V1.0
 * 修改人： 王浩然
 * 修改内容：创建
 **********************************************************/

// 目的: 实现任意两个公交站之间的最短路径,最小花费查询,并支持删除,插入操作

/**********************测试样例*****************************
 *    9
 *    8
 *    1 2 2 3
 *    1 4 1 4
 *    2 6 3 7
 *    4 6 6 9
 *    5 3 11 12
 *    2 7 17 21
 *    3 7 100 100
 *    8 9 0 0
 **********************************************************/

/**********************ADT*****************************
 *    ADT BusStop:
 *        数据:
 *            int dist[N] : 储存的是每个点的最短距离
 *            int e[N], ne[N], h[N], idx, w[N], dis[N], cnt[N] : 邻接表
 *            int topo_e[N], topo_ne[N], topo_idx, topo_dis[N], topo_h[N], du[N] :拓扑中的新图
 *            int n, m, op : n个点,m条边,op代表操作
 *            int st_min_dist, ed_min_dist : 最短路径---公交的起点和终点
 *            int st_min_cost, ed_min_cost : 最小花费--公交的起点和终点
 *            int st_c_and_d, ed_c_and_d : 最短路径和最小花费的条数
 *            int make_delete_st, make_delete_ed : 删除的两个点
 *            int make_new_st, make_new_ed : 新增的两个点
 *            int pre[N], path[N] : 记录前驱节点和路径
 *            vector<int>A_star_path[N], A_star_dist, bus_line : A*算法中的路径储存,以及公交站点的储存
 *            typedef pair<int, int>pii : 将pair重定义
 *            map<pii, bool>mp : 用于公交站的删除和插入
 *            map<int, bool>bus : 用于判断公交站点
 *            bool vis[N] : 判断哪些公交站出没出现过
 *        操作:
 *            void create_BusStop() : 进行建图操作
 *            void add() : 用于进行建图
 *            void A-star() : 使用A*算法进行计算第k短路径
 *            void dijkstra_dist() : 计算单源汇最短距离
 *            void dijkstra_cost() : 计算单源汇最短花费
 *            void query_dist() : 输出最短距离
 *            void query_cost() : 输出最小花费
 *            void quert_count_dist_and_cost() : 计算有多少条最短路径
 *            void make_delete() : 删除两站的一条边
 *            void make_new() : 新增两站的一条边
 *            void get_bus_line() : 获取所有的站点信息
 *            void get_bus_single() : 获取单点站的信息
 *            pprint() : 打印操作信息
 **********************************************************/

/**********************储存和算法分析***************************
 *    - 对于数据的存储结构,对于一些常变量例如 cost 以及 dist 等等,使用全局变量储存
 *        理由: 1.方便用户进行实时的更改和变动
 *             2.易于进行访问,无需通过参数传递
 *             3.避免内存浪费,避免在每个函数中重复分配和释放内存的开销
 *             4. 共享状态,易于编写代码和逻辑清晰
 *
 *    - 对于公交站点的路径花费以及距离的储存,这里采用用数组模拟的邻接表进行储存
 *        理由: 1.紧凑的储存,使用数组，存储空间是紧凑的，每个元素在内存中相邻
 *                相比于其他数据结构，这有助于提高内存访问效率，因为数组元素之间没有额外的指针或链接
 *              2.快速的随机访问：可以直接通过索引快速访问任意公交站点的邻接信息，而无需遍历整个数据结构
 *              3.简单直观,易于理解和实现
 *              4.适用于稠密图： 如果公交站点之间的连接比较密集，即大多数站点之间都存在边，使用数组模拟邻接表可以更有效地利用内存
 *              5.遍历效率高
 *
 *    - 对于A*算法中的变量,使用结构体进行储存
 *        理由: 1.成员变量名清晰,有助于提高代码的可维护性
 *             2.将成员变量进行封装,具有逻辑性,更易于理解
 *             3.可以利用重载运算符进行比较和排序,便于编写代码
 *
 *    - 对于各个路径之间的变量值和联系,这里使用了优先队列(小根堆)来储存
 *        理由: 1.每次都能够快速的访问节点中的最短距离或者函数的最小期望,易于dijkstra算法和A*的实现
 *             2.时间复杂度较小,便于维护,相较于朴素dijkstra更加快速
 *             3.能够在搜索过程中快速获取当前最有希望的节点，提高算法的效率
 *             4.自定义优先队列操作：实现了向上调整 AdjustUp 和向下调整 AdjustDown 操作，这是优先队列的基本操作，确保了队列的维护
 **********************************************************/

#include <stdexcept>
#include <algorithm>
#include <windows.h>
#include <iostream>
#include <numeric>
#include <cstring>
#include <utility>
#include <chrono>
#include <thread>
#include <memory>
#include <vector>
#include <queue>
#include <cmath>
#include <set>
#include <map>

using namespace std;
/**********************实现小根堆*****************************
***********************************************************/
namespace priority
{
    /*********************************************************
     * 功能描述：实现内部的根堆的数据结构
     ************************************************************/
    // 比较方式（使内部结构为大堆）
    template <class T>
    class Less
    {
    public:
        bool operator()(const T &x, const T &y)
        {
            return x < y;
        }
    };
    // 比较方式（使内部结构为小堆）
    template <class T>
    class Greater
    {
    public:
        bool operator()(const T &x, const T &y)
        {
            return x > y;
        }
    };

    template <class T, class Container = vector<T>, class Compare = Less<T>>
    class priority_queue
    {
    public:
        priority_queue()
        {
        }

        template <class InputIterator>
        priority_queue(InputIterator first, InputIterator last)
        {
            // 将迭代器中的数据插入优先级队列中
            while (first != last)
            {
                _con.push_back(*first);
                first++;
            }
            // 从最后一个非叶子结点向下调整
            for (int i = (_con.size() - 1 - 1) / 2; i >= 0; i--)
            {
                AdjustDown(i);
            }
        }
        // 堆的向上调整
        void AdjustUp(size_t child)
        {
            size_t parent = (child - 1) / 2; // 找到父节点
            while (child > 0)
            {
                if (_com(_con[parent], _con[child])) // 判断是否需要交换
                {
                    // 交换父子结点
                    swap(_con[parent], _con[child]);
                    // 继续向上调整
                    child = parent;
                    parent = (child - 1) / 2;
                }
                else
                {
                    break;
                }
            }
        }
        // 向下调整
        void AdjustDown(size_t parent)
        {
            size_t child = parent * 2 + 1; // 算出左子节点的下标
            while (child < _con.size())
            {
                // 找出子结点中符合比较方式的值
                if (child + 1 < _con.size() && _com(_con[child], _con[child + 1]))
                {
                    child++;
                }
                // 通过所给比较方式确定是否需要交换结点位置
                if (_com(_con[parent], _con[child]))
                {
                    // 交换父子结点
                    swap(_con[parent], _con[child]);
                    // 继续向下调整
                    parent = child;
                    child = parent * 2 + 1;
                }
                else
                {
                    break;
                }
            }
        }
        // 插入数据
        void push(const T &x)
        {
            _con.push_back(x);
            AdjustUp(_con.size() - 1); // 将最后一个元素向上调整
        }
        // 删除数据
        void pop()
        {
            swap(_con[0], _con[_con.size() - 1]); // 交换首尾数据
            _con.pop_back();                      // 尾删
            AdjustDown(0);                        // 首元素向下调整
        }
        // 访问头元素
        const T &top() const
        {
            return _con[0];
        }
        // 获取队列中有效元素个数
        size_t size()
        {
            return _con.size();
        }
        // 判空
        bool empty()
        {
            return _con.empty();
        }

    private:
        Container _con; // 底层容器
        Compare _com;   // 比较方式
    };
}

const int N = 1e5 + 10;

int dist[N]; // 储存的是每个点的最短距离

int e[N], ne[N], h[N], idx, w[N], dis[N], cnt[N]; // 邻接表

int topo_e[N], topo_ne[N], topo_idx, topo_dis[N], topo_h[N], du[N]; // 拓扑中的新图

int n, m, op; // n个点,m条边,op代表操作

int st_min_dist, ed_min_dist; // 最短路径---公交的起点和终点

int st_min_cost, ed_min_cost; // 最小花费--公交的起点和终点

int st_c_and_d, ed_c_and_d; // 最短路径和最小花费的条数

int make_delete_st, make_delete_ed; // 删除的两个点

int make_new_st, make_new_ed; // 新增的两个点

int min_change_st, min_change_ed; // 转点的起点和终点

int pre[N], path[N]; // 记录前驱节点和路径

int p[N]; // 用于构建并查集

vector<int> A_star_path[N], A_star_dist, bus_line; // A*算法中的路径储存,以及公交站点的储存
typedef pair<int, int> pii;
map<pii, bool> mp;  // 用于公交站的删除和插入
map<int, bool> bus; // 用于判断公交站点
bool vis[N], vis_bus[N];

struct node
{
    int pos, g, f;
    // g为从源点s到当前点p所走的路径长度，f为A*算法（也就是类似启发式搜索）的F值
    node(int pos = 0, int g = 0, int f = 0) : pos(pos), g(g), f(f) {}
    bool operator<(const node &w) const
    {
        if (w.f == f)
            return w.g < g;
        return w.f < f;
    }
};

struct Edge
{
    int u, v, w;
    bool operator<(const Edge &W) const
    {
        return w < W.w;
    }
};

/********************添加站点*****************************
 * 功能描述：添加站点
 * 输入参数：起始边,终止边,道路的花费和距离
 * 输出参数：无
 * 返回值： 无
 * 其它说明：无
 ************************************************************/
void add(int a, int b, int c, int d)
{

    // 进行图的存储,这里使用的邻接表储存图
    e[idx] = b, w[idx] = c, dis[idx] = d, ne[idx] = h[a], h[a] = idx++;
}

/*****************A-star算法计算第k短距离**********************
 * 功能描述：A-star算法计算第k短距离
 * 输入参数： 起点,终点,k
 * 输出参数： 无
 * 返回值： void
 * 其它说明：用于计算
 ************************************************************/
bool A_star(int st, int ed, int k)
{
    int num = 0, check = 0;
    A_star_dist.clear();
    if (st == ed)
        k++;

    if (dist[st] >= 0x3f3f3f3f / 2)
        return false;

    priority_queue<node> que;
    que.push(node(st, 0, dist[st]));

    while (!que.empty())
    {
        node now = que.top();
        que.pop();

        // A_star_path[num].push_back(now.pos);
        if (now.pos == ed)
        {
            check = 1;
            num++;
            A_star_dist.push_back(now.g);
            // A_star_path[num].push_back(st);
        }
        if (num == k)
            return true;
        for (int i = h[now.pos]; ~i; i = ne[i])
        {
            node nex;

            if (e[i] == -1)
                continue;

            nex.pos = e[i];
            nex.g = now.g + dis[i];
            // cout<<e[i]<<' '<<dis[i]<<' '<<nex.g<<endl;
            nex.f = (now.g + dis[i]) + dist[e[i]];
            que.push(nex);
        }
    }
    return false;
}

/******************使用dijkstra算法计算最短路*******************
 * 功能描述：使用dijkstra算法计算最短路
 * 输入参数： 起点
 * 输出参数： 从起点到终点的最短路径
 * 返回值： void
 ************************************************************/
void dijkstra_dist(int st)
{
    /**
    对于求任意两点之间的最短路径和最小花费,这里使用的Dijkstra算法来计算
    时间复杂度是N*logN,可以满足10000000的数据范围
    **/
    memset(dist, 0x3f, sizeof dist);
    memset(vis, false, sizeof vis);
    memset(pre, 0, sizeof pre);

    dist[st] = 0;                                       // 起点设为0
    priority_queue<pii, vector<pii>, greater<pii>> que; // 使用优先队列,即小根堆进行维护
    que.push({0, st});                                  // 起点入队
    cnt[st] = 1;
    while (!que.empty())
    {
        auto now = que.top(); // 取出小根堆堆顶元素
        que.pop();            // 取出来了就要出队

        int now_dist = now.first, now_id = now.second; // 第一个元素是目前的距离,第二个元素是当前的公交站点
        if (vis[now_id])
            continue;       // 如果当前点被查询过,跳过
        vis[now_id] = true; // 标记查询过了

        for (int i = h[now_id]; ~i; i = ne[i])
        {
            int j = e[i];
            if (j == -1)
                continue;

            if (dist[j] == now_dist + dis[i])
                cnt[j] += cnt[now_id];

            if (dist[j] > now_dist + dis[i])
            {
                pre[j] = now_id;
                dist[j] = now_dist + dis[i];
                cnt[j] = cnt[now_id];
                que.push({dist[j], j});
            }
        }
    }
}

/*******************dijkstra算法计算最小花费***************
 * 功能描述：dijkstra算法计算最小花费
 * 输入参数： 起点
 * 输出参数： 从起点到终点的最小花费
 * 返回值： void
 * 其它说明：无
 ************************************************************/
void dijkstra_cost(int st)
{
    memset(dist, 0x3f, sizeof dist);
    memset(vis, false, sizeof vis);
    memset(pre, 0, sizeof pre);

    dist[st] = 0;                                       // 起点设为0
    priority_queue<pii, vector<pii>, greater<pii>> que; // 使用优先队列,即小根堆进行维护
    cnt[st] = 1;
    que.push({0, st}); // 起点入队

    while (!que.empty())
    {
        auto now = que.top(); // 取出小根堆堆顶元素
        que.pop();            // 取出来了就要出队

        int now_dist = now.first, now_id = now.second; // 第一个元素是目前的距离,第二个元素是当前的公交站点
        if (vis[now_id])
            continue;       // 如果当前点被查询过,跳过
        vis[now_id] = true; // 标记查询过了

        for (int i = h[now_id]; ~i; i = ne[i])
        { // 处理
            int j = e[i];
            if (j == -1)
                continue;

            if (dist[j] == now_dist + w[i])
                cnt[j] += cnt[now_id];

            if (dist[j] > now_dist + w[i])
            {
                pre[j] = now_id;
                dist[j] = now_dist + w[i];
                cnt[j] = cnt[now_id];
                que.push({dist[j], j});
            }
        }
    }
}

/***************查询并输出两点间最短路径*******************
 * 功能描述：查询并输出两点间最短路径
 * 输入参数： 操作数
 * 输出参数： 根据具体操作数进行输出
 * 返回值： void
 * 其它说明：无
 ************************************************************/
void query_min_dist(int operate)
{
    /**
    对于求任意两点之间的最短路径和最小花费,这里使用的Dijkstra算法来计算
    时间复杂度是N*logN,可以满足10000000的数据范围
    **/
    cout << "请输入要查询最短路径的起点和终点: ";
    cin >> st_min_dist >> ed_min_dist;

    dijkstra_dist(st_min_dist);

    if (dist[ed_min_dist] >= 0x3f3f3f3f / 2)
    {
        cout << endl
             << "无法到达!" << endl
             << endl;

        Sleep(1500);
        return;
    }
    else if (operate == 1)
        cout << endl
             << "从起点到终点的的最短距离为: " << dist[ed_min_dist] << endl
             << endl;

    memset(path, -1, sizeof path);
    if (operate == 1)
        cout << "最短路径为: ";
    int tmp1, tmp2, cnt = 1;
    path[1] = ed_min_dist;

    for (int i = 0; !(tmp2 == st_min_dist); ++i)
    {
        if (i == 0)
            tmp1 = ed_min_dist;
        else
        {
            tmp2 = pre[tmp1];
            path[++cnt] = tmp2;
            tmp1 = tmp2;
        }
    }

    if (operate == 1)
    {
        for (int i = cnt; i >= 2; i--)
            cout << path[i] << " -> ";
        cout << path[1] << endl;
    }

    if (operate == 3)
    {
        cout << "请输入你需要查询前k短路径: ";
        int oper;
        cin >> oper;
        if (oper == -1)
            return;
        else
        {

            dijkstra_dist(ed_min_dist);

            if (!A_star(st_min_dist, ed_min_dist, oper))
                cout << "数量不够" << endl;
            else
            {
                for (int i = 0; i < oper; i++)
                {
                    cout << "第 " << i + 1 << " 条最短路径的长度为: " << A_star_dist[i] << endl;
                    // if(i>0) cout<<st_min_dist<<' ';
                    for (auto u : A_star_path[i])
                        cout << u << ' ';
                    cout << endl;
                }
            }
        }
    }

    Sleep(1500);
    return;
}

/****************查询并输出两点间最小花费*********************
 * 功能描述：查询并输出两点间最小花费
 * 输入参数： 操作数
 * 输出参数： 根据具体操作数进行输出
 * 返回值： void
 * 其它说明：无
 ************************************************************/
void query_min_cost()
{
    cout << "请输入要查询最小花费的起点和终点: ";
    cin >> st_min_dist >> ed_min_dist;

    dijkstra_cost(st_min_dist);

    if (dist[ed_min_dist] >= 0x3f3f3f3f / 2)
    {
        cout << endl
             << "无法到达!" << endl
             << endl;
        Sleep(1500);
        return;
    }
    else
        cout << endl
             << "从起点到终点的最小花费为: " << dist[ed_min_dist] << endl
             << endl;

    memset(path, -1, sizeof path);
    cout << "最小花费路径为: ";
    int tmp1, tmp2, cnt = 1;
    path[1] = ed_min_dist;

    for (int i = 0; !(tmp2 == st_min_dist); ++i)
    {
        if (i == 0)
            tmp1 = ed_min_dist;
        else
        {
            tmp2 = pre[tmp1];
            path[++cnt] = tmp2;
            tmp1 = tmp2;
        }
    }
    for (int i = cnt; i >= 2; i--)
        cout << path[i] << " -> ";
    cout << path[1] << endl;

    Sleep(1500);
    return;
}

/****************查询最短路和最小花费路径条数*****************
 * 功能描述：查询最短路和最小花费路径条数
 * 输入参数： 无
 * 输出参数： 路径条数
 * 返回值： void
 * 其它说明：无
 ************************************************************/
void quert_count_dist_and_cost()
{
    query_min_dist(1);
    cout << "最短路径最多有: " << cnt[ed_min_dist] << "条" << endl;
    query_min_cost();
    cout << "最少花费路径最多有: " << cnt[ed_min_dist] << "条" << endl;
    Sleep(1500);
}

/*************广度优先搜索算出最小中转次数*********************
 * 功能描述：广度优先搜索算出最小中转次数
 * 输入参数： 起点和终点
 * 输出参数： 中转次数以及路径输出
 * 返回值： void
 * 其它说明：无
 ************************************************************/
void get_min_change()
{
    // 这里使用广度优先搜索 Bfs
    memset(vis_bus, false, sizeof vis_bus);
    queue<pii> que;
    cout << "请输出你想查询的起点与终点: ";
    cin >> min_change_st >> min_change_ed;
    que.push({0, min_change_st});

    dijkstra_dist(min_change_st);
    if (dist[min_change_ed] >= 0x3f3f3f3f / 2)
    {
        cout << endl
             << "无法到达!" << endl
             << endl;
        Sleep(1500);
        return;
    }

    while (!que.empty())
    {
        pii now = que.front();
        que.pop();
        int step = now.first, stop = now.second;
        vis_bus[stop] = true;

        for (int i = h[stop]; ~i; i = ne[i])
        {
            int j = e[i];
            if (j == -1)
                continue;
            if (!vis_bus[j])
            {
                que.push({step + 1, j});
                pre[j] = stop;

                if (j == min_change_ed)
                {
                    cout << "所需要的最小中转次数为: " << step << endl;
                    goto next;
                }
            }
        }
    }

next:;
    int tmp1, tmp2, cnt = 1;
    path[1] = min_change_ed;

    cout << "其最小中转次数的路径为: ";
    for (int i = 0; !(tmp2 == min_change_st); ++i)
    {
        if (i == 0)
            tmp1 = min_change_ed;
        else
        {
            tmp2 = pre[tmp1];
            path[++cnt] = tmp2;
            tmp1 = tmp2;
        }
    }
    for (int i = cnt; i >= 2; i--)
        cout << path[i] << "->";
    cout << path[1] << endl;

    Sleep(1500);
    return;
}

/***************并查集的修改操作************************
 * 功能描述：并查集的修改操作
 * 输入参数：修改点
 * 输出参数： 无
 * 返回值：  修改点x的祖先
 * 其它说明：无
 ************************************************************/
int find(int x)
{
    if (x != p[x])
        p[x] = find(p[x]);
    return p[x];
}

/****************查询最小生成树***************
 * 功能描述：查询还有多少车站不能驶向其它车站
 * 输入参数：无
 * 输出参数： 无
 * 返回值： 无
 * 其它说明：无
 ************************************************************/
void query_last_number()
{
    int cnt = 0, u_cnt = 0;
    Edge edge[N];
    for (auto bus_ : bus_line)
        p[bus_] = bus_;
    for (auto bus_ : bus_line)
    {
        if (bus[bus_])
        {
            for (int i = h[bus_]; ~i; i = ne[i])
            {
                int j = e[i];
                if (j == -1)
                    continue;
                edge[u_cnt] = {bus_, j, dis[i]};
                edge[++u_cnt] = {j, bus_, dis[i]};
                if (find(bus_) != find(j))
                {
                    p[find(bus_)] = find(j);
                    cnt++;
                }
            }
        }
    }

    int count_number = 0;
    map<int, vector<int>> count_bus_stop;
    set<int> bus_vis;
    for (auto bus_ : bus_line)
    {
        if (bus[bus_])
        {
            if (p[bus_] == bus_)
                count_number++;
            bus_vis.insert(p[bus_]), count_bus_stop[p[bus_]].push_back(bus_);
        }
    }
    if (count_number == 1)
    {
        cout << "该公交站能够周游一圈 " << endl;

        int answer = 0;
        for (auto bus_ : bus_line)
            p[bus_] = bus_;
        sort(edge, edge + u_cnt);

        for (int i = 0; i < u_cnt; i++)
        {
            int u = edge[i].u, v = edge[i].v, w = edge[i].w;
            if (find(u) != find(v))
            {
                p[find(u)] = find(v);
                answer += w;
            }
        }

        cout << "周游一圈的最小距离权值为: " << answer << endl;
    }
    else
    {
        cout << "任意站点之间不能互相到达其它站点!" << endl
             << endl
             << endl;
        cout << "一共有 " << count_number << " 个互相连通的公交站,分别是: " << endl;
        count_number = 1;
        for (auto bus_ : bus_vis)
        {
            cout << "---------------第 " << count_number++ << " 个--------------- " << endl;
            for (auto bus__ : count_bus_stop[bus_])
                cout << bus__ << " 站 ";
            cout << endl
                 << "-------------------------------------" << endl;
        }
    }

    Sleep(1200);
    return;
}

/*****************进行站点之间的删除***********************
 * 功能描述：进行站点之间的删除
 * 输入参数： 起点和终点
 * 输出参数： 无
 * 返回值： 0-成功   其他-失败
 * 其它说明：无
 ************************************************************/
void make_delete()
{
    /**
    该函数为对图的节点删除,时间复杂度为N
    **/
    cout << "请输入废除的两个公交站的起点和终点: ";
    cin >> make_delete_st >> make_delete_ed;

    bool flag_all = false;
    for (int i = h[make_delete_st]; ~i; i = ne[i])
    {
        int j = e[i];
        if (j == make_delete_ed)
        {
            flag_all = true;
            e[i] = -1;
            cout << endl
                 << "删除成功↖(^ω^)↗!" << endl
                 << endl;
        }
    }

    for (int i = h[make_delete_ed]; ~i; i = ne[i])
    {
        int j = e[i];
        if (j == make_delete_st)
            e[i] = -1;
    }

    for (auto bus_ : bus_line)
    {
        bool flag = false;
        for (int i = h[bus_]; ~i; i = ne[i])
        {
            int j = e[i];
            if (j != -1)
            {
                flag = true;
                break;
            }
        }
        if (!flag)
            bus[bus_] = false;
        else
            bus[bus_] = true;
    }
    if (!flag_all)
        cout << endl
             << "该路线不存在(╥﹏╥)!" << endl
             << endl;
    Sleep(1000);
    return;
}

/********************增加两个站点************************
 * 功能描述：增加两个站点
 * 输入参数： 起点和终点
 * 输出参数： 无
 * 返回值： 0-成功   其他-失败
 * 其它说明：无
 ************************************************************/
void make_new()
{
    /**
    该函数为对图的节点增加,时间复杂度为N
    **/
    cout << "请输入新增的两个公交站路线并输入花费和距离: ";
    int cost, dist_;

    cin >> make_new_st >> make_new_ed >> cost >> dist_;

    for (int i = h[make_new_st]; ~i; i = ne[i])
    {
        int j = e[i];
        if (j == make_new_st)
        {
            cout << "该路线已经存在(╥﹏╥)!" << endl;
            Sleep(1500);
            return;
        }
    }

    // 添加边,并且如果出现未出现的站点,将其储存
    add(make_new_st, make_new_ed, cost, dist_), add(make_new_ed, make_new_st, cost, dist_);
    if (!bus[make_new_st])
        bus[make_new_st] = true;
    if (!bus[make_new_ed])
        bus[make_new_ed] = true;

    cout << endl
         << "添加成功↖(^ω^)↗!" << endl
         << endl;

    for (auto bus_ : bus_line)
    {
        bool flag = false;
        for (int i = h[bus_]; ~i; i = ne[i])
        {
            int j = e[i];
            if (j != -1)
            {
                flag = true;
                break;
            }
        }
        if (!flag)
            bus[bus_] = false;
        else
            bus[bus_] = true;
    }
    Sleep(1000);
    return;
}

/****************查询所有的公交站信息************************
 * 功能描述：查询所有的公交站信息
 * 输入参数： 无
 * 输出参数： 站点的详细信息
 * 返回值： 0-成功   其他-失败
 * 其它说明：无
 ************************************************************/
void get_busline_all()
{
    cout << "目前所有存在的站点有: " << endl;
    for (auto bustop : bus_line)
    {
        if (bus[bustop])
        {
            cout << "----------当前的站点是: " << bustop << "站-----------" << endl;
            cout << "关于该站的详细信息: " << endl;
            for (int i = h[bustop]; ~i; i = ne[i])
            {
                int j = e[i];
                if (j != -1)
                    cout << "该站与 " << j << "站 相邻,两站的距离是" << dis[i] << "米,两站之间的花费为: " << w[i] << "元" << endl;
            }
        }
    }
    cout << endl;
    Sleep(1500);
}

/****************查询单个站点的详细信息**********************
 * 功能描述：查询单个站点的详细信息
 * 输入参数： 站点
 * 输出参数： 该站点的详细信息
 * 返回值： 0-成功   其他-失败
 * 其它说明：无
 ************************************************************/
void get_busline_single()
{
    int now_bus;
    cout << "请输入你想查询的站点: ";
    cin >> now_bus;
    if (!bus[now_bus])
        cout << endl
             << "该站点不存在或已被删除(╥﹏╥)" << endl;
    else
    {
        cout << "----------当前的站点是: " << now_bus << "站-----------" << endl;
        cout << "关于该站的详细信息: " << endl;
        for (int i = h[now_bus]; ~i; i = ne[i])
        {
            int j = e[i];
            if (e[i] != -1)
                cout << "该站与 " << e[i] << "站相邻,两站的距离是" << dis[i] << "米,两站之间的花费为: " << w[i] << "元" << endl
                     << endl;
        }
    }
    Sleep(1500);
}

/*****************建立公交路线************************
 * 功能描述：建立公交路线
 * 输入参数： 公交站的数目以及路线
 * 输出参数： 无
 * 返回值： 0-成功   其他-失败
 * 其它说明：无
 ************************************************************/
void create_BusStop()
{
    cout << "请输入公交站的总数目: ";
    cin >> n;

    cout << endl
         << "请输出公交站之间的总路线数量: ";
    cin >> m;

    cout << endl
         << "请输入公交站互相之间的关系(起点,终点,花费,距离): " << endl;
    cout << "注意: 若您输入重复的边系统将覆盖上一条边,本系统中不允许重边和自环的存在" << endl
         << endl;
    memset(h, -1, sizeof h);

    for (int i = 1; i <= m; i++)
    {
        int u, v, c, d;
        cin >> u >> v >> c >> d;
        add(u, v, c, d), add(v, u, c, d); // 存边
        if (!bus[u])
        {
            bus_line.push_back(u);
            bus[u] = true;
        }
        if (!bus[v])
        {
            bus_line.push_back(v);
            bus[v] = true;
        }
    }
}

/*****************打印操作******************************
 * 功能描述：打印操作
 * 输入参数：无
 * 输出参数：无
 * 返回值： 无
 * 其它说明：无
 ************************************************************/
void pprint()
{
    cout << endl
         << endl;
    cout << "请输入你想查询的信息 ↖(^ω^)↗ (输入-1表示查询结束): " << endl;
    cout << "1 : 查询两个公交站的最短路径" << endl;                   /// 时间复杂度nlogn
    cout << "2 : 查询两个公交站的最省钱的路径" << endl;               /// 时间复杂度nlogn
    cout << "3 : 查询前k短个路径(站点可重复经过)" << endl;            // 时间复杂度nlogn
    cout << "4 : 查询两个公交站最短路径和最省钱的路径有几条" << endl; // 时间复杂度nlogn
    cout << "5 : 废除两个公交站路线: " << endl;                       /// 时间复杂度n
    cout << "6 : 新增两个公交站路线: " << endl;                       /// 时间复杂度n
    cout << "7 : 获取所有公交站点序列" << endl;                       // 时间复杂度n
    cout << "8 : 获取单个公交站点的详细信息" << endl;                 // 时间复杂度n
    cout << "9 : 获取两城市之间需要中转次数最小的路线" << endl;
    cout << "10: 获取哪些车站之间能够互相到达以及公交站的最小权值和" << endl;
    cout << endl
         << endl
         << "请输入操作: ";
}

int main()
{
    create_BusStop(); // 建图

    pprint();

    while (cin >> op, op != -1)
    {

        if (op == 1)
            query_min_dist(1);

        else if (op == 2)
            query_min_cost();

        else if (op == 3)
            query_min_dist(3);

        else if (op == 4)
            quert_count_dist_and_cost();

        else if (op == 5)
            make_delete();

        else if (op == 6)
            make_new();

        else if (op == 7)
            get_busline_all();

        else if (op == 8)
            get_busline_single();

        else if (op == 9)
            get_min_change();

        else if (op == 10)
            query_last_number();

        else
            cout << "该功能不存在(╥﹏╥),我们正在改进,请重新输入你想要的功能ovo!" << endl;

        pprint();
    }

    cout << endl
         << "祝您路途愉快 ↖(^ω^)↗!" << endl;

    return 0;
}
