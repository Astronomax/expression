#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <chrono>
#include <random>
#include <set>
#include <map>
#include <queue>
#include <deque>
#include <string>
#include <unordered_map>
#include <algorithm>
#include <cassert>
using namespace std;

#define all(X) begin(X), end(X)
#define mp make_pair
//#define int long long

namespace parser {
    enum class node_t {
        CONCAT,
        ALTER,
        KLEENE,
        LETTER,
        ANY
    };

    struct node {
        node_t t;
        char c;
        node *l, *r;
        node(node_t t_, char c_, node *l_, node *r_) :
            t(t_), c(c_), l(l_), r(r_) {}
    };

    struct parser {
        string t;
        unordered_map<int, vector<int>> alt, con, kle;
        vector<int> bal;

        parser(const string &s) {
            t = { s[0] };
            for (int i = 1; i < s.size(); i++) {
                if (s[i - 1] != '(' && s[i] != ')')
                    if (s[i - 1] != '|' && s[i] != '|' && s[i] != '*')
                        t.push_back('_');
                t.push_back(s[i]);
            }
            bal.resize(t.size() + 1);
            for (int i = 0; i < t.size(); i++) {
                bal[i + 1] = bal[i];
                if (t[i] == '(') bal[i + 1]++;
                else if (t[i] == ')') bal[i + 1]--;
            }
            for (int i = 0; i < t.size(); i++) {
                if (t[i] == '|')
                    alt[bal[i + 1]].push_back(i);
                else if (t[i] == '_')
                    con[bal[i + 1]].push_back(i);
                else if (t[i] == '*')
                    kle[bal[i + 1]].push_back(i);
            }
        }

        node *parse(int l, int r) {
            if (l >= r) return nullptr;
            else if (l + 1 == r) {
                if (t[l] == '.')
                    return new node(node_t::ANY, '#', nullptr, nullptr);
                else if ('a' <= t[l] && t[l] <= 'z')
                    return new node(node_t::LETTER, t[l], nullptr, nullptr);
                else return nullptr;
            }
            else {
                int _con = -1, _alt = -1, _kle = -1;
                auto it = lower_bound(all(con[bal[l]]), r);
                if (it != con[bal[l]].begin())
                    _con = *(--it);
                if (_con < l) _con = -1;
                it = lower_bound(all(alt[bal[l]]), r);
                if (it != alt[bal[l]].begin())
                    _alt = *(--it);
                if (_alt < l) _alt = -1;
                it = lower_bound(all(kle[bal[l]]), r);
                if (it != kle[bal[l]].begin())
                    _kle = *(--it);
                if (_kle < l) _kle = -1;

                if (_alt != -1) {
                    node *l_ = parse(l, _alt);
                    node *r_ = parse(_alt + 1, r);
                    if (l_ == nullptr) return r_;
                    else if (r_ == nullptr) return l_;
                    else return new node(node_t::ALTER, '#', l_, r_);
                }
                else if (_con != -1) {
                    node *l_ = parse(l, _con);
                    node *r_ = parse(_con + 1, r);
                    if (l_ == nullptr) return r_;
                    else if (r_ == nullptr) return l_;
                    else return new node(node_t::CONCAT, '#', l_, r_);
                }
                else if (_kle != -1) {
                    node *l_ = parse(l, _kle);
                    if (l_ == nullptr)
                        return nullptr;
                    else return new node(node_t::KLEENE, '#', l_, nullptr);
                }
                else return parse(l + 1, r - 1);
            }
        }

        node *parse() {
            return parse(0, t.size());
        }
    };
};

namespace dfa {
    struct node {
        int id = -1;
        vector<node*> edges[26];
        vector<node*> eps;
        node() = default;
    };

    struct dfa {
        int n;
        node *start, *finish;
        dfa(node *start_, node* finish_) :
            start(start_), finish(finish_) {}
    };

    int numerate(node *v, int mex) {
        if (v->id != -1) return mex;
        v->id = mex++;
        for (int i = 0; i < 26; i++)
            for (auto &j : v->edges[i])
                mex = numerate(j, mex);
        for (auto &j : v->eps)
            mex = numerate(j, mex);
        return mex;
    }

    dfa *__build_dfa(parser::node *v) {
        dfa *res = new dfa(new node(), new node());
        if (v == nullptr)
            res->start->eps.push_back(res->finish);
        else if (v->t == parser::node_t::CONCAT) {
            dfa *l = __build_dfa(v->l);
            dfa *r = __build_dfa(v->r);
            res->start->eps.push_back(l->start);
            l->finish->eps.push_back(r->start);
            r->finish->eps.push_back(res->finish);
        }
        else if (v->t == parser::node_t::ALTER) {
            dfa *l = __build_dfa(v->l);
            dfa *r = __build_dfa(v->r);
            res->start->eps.push_back(l->start);
            res->start->eps.push_back(r->start);
            l->finish->eps.push_back(res->finish);
            r->finish->eps.push_back(res->finish);
        }
        else if (v->t == parser::node_t::KLEENE) {
            res = __build_dfa(v->l);
            
            for (int i = 0; i < 26; i++) {
                set<node*> order(all(res->finish->edges[i]));
                for(auto &j : res->start->edges[i])
                    order.insert(j);
                res->finish->edges[i].clear();
                res->finish->edges[i].resize(order.size());
                copy(order.begin(), order.end(), res->finish->edges[i].begin());
            }
            set<node*> order(all(res->finish->eps));
            for(auto &j : res->start->eps)
                order.insert(j);
            res->finish->eps.clear();
            res->finish->eps.resize(order.size());
            copy(order.begin(), order.end(), res->finish->eps.begin());

            res->start->eps.push_back(res->finish);
        }
        else if (v->t == parser::node_t::LETTER)
            res->start->edges[v->c - 'a'].push_back(res->finish);
        else if (v->t == parser::node_t::ANY) {
            for (int i = 0; i < 26; i++)
                res->start->edges[i].push_back(res->finish);
        }
        return res;
    }

    dfa *build_dfa(parser::node *v) {
        dfa *res = __build_dfa(v);
        res->n = numerate(res->start, 0);
        return res;
    }
};

const int MAXN = 40100, INF = 1e9;
int dp[2][MAXN];
int dplink[2][MAXN];
bool _used[MAXN];

namespace graph {
    struct node {
        vector<int> l[26];
        vector<int> e;
    };

    struct graph {
        int n;
        node *g;
    };

    graph dfa_to_graph(dfa::dfa *d) {
        //cout << d->n << endl;
        graph res = { d->n, new node[d->n] };
        assert(d->n >= 0);
        vector<bool> used(d->n);

        queue<dfa::node*> que;
        que.push(d->start);
        used[d->start->id] = 1;

        while (!que.empty()) {
            dfa::node *v = que.front();
            que.pop();
            for (int i = 0; i < 26; i++) {
                for (auto &u : v->edges[i]) {
                    if (!used[u->id]) {
                        que.push(u);
                        used[u->id] = 1;
                    }
                    res.g[v->id].l[i].push_back(u->id);
                }
            }
            for (auto &u : v->eps) {
                if (!used[u->id]) {
                    que.push(u);
                    used[u->id] = 1;
                }
                res.g[v->id].e.push_back(u->id);
            }
        }
        return res;
    }

    graph inverse(graph g) {
        graph res = { g.n, new node[g.n] };
        vector<bool> used(g.n);

        for (int start = 0; start < res.n; start++) {
            if (used[start]) continue;
            queue<int> que;
            que.push(start);
            used[start] = 1;

            while (!que.empty()) {
                int v = que.front();
                que.pop();
                for (int i = 0; i < 26; i++) {
                    for (auto &u : g.g[v].l[i]) {
                        if (!used[u]) {
                            que.push(u);
                            used[u] = 1;
                        }
                        res.g[u].l[i].push_back(v);
                    }
                }
                for (auto &u : g.g[v].e) {
                    if (!used[u]) {
                        que.push(u);
                        used[u] = 1;
                    }
                    res.g[u].e.push_back(v);
                }
            }
        }
        return res;
    }

    struct distres {
        int start;
        vector<int> dist;
        vector<pair<int, char>> pred;
    };

    distres dist(int start, graph g) {
        distres res;
        deque<int> que;
        res.start = start;
        res.dist.assign(g.n, INF);
        res.pred.assign(g.n, make_pair(-1, '#'));
        que.push_front(start);
        res.dist[start] = 0;

        while (!que.empty()) {
            int v = que.front();
            que.pop_front();

            for (int i = 0; i < 26; i++) {
                for (auto &u : g.g[v].l[i]) {
                    if (res.dist[v] + 1 < res.dist[u]) {
                        que.push_back(u);
                        res.dist[u] = res.dist[v] + 1;
                        res.pred[u] = { v, 'a' + i };
                    }
                }
            }
            for (auto &u : g.g[v].e) {
                if (res.dist[v] < res.dist[u]) {
                    que.push_front(u);
                    res.dist[u] = res.dist[v];
                    res.pred[u] = { v, '#' };
                }
            }
        }
        return res;
    }

    struct condensator {
        struct condensation {
            vector<int> colors;
            graph condensed;
        };

        graph g, invg;
        vector<int> euler;
        vector<bool> used;
        condensation res;

        condensator(graph g_) : g(g_) {
            used.resize(g.n);
            invg = inverse(g);
            res.colors.assign(g.n, -1);
        }

        void get_euler(int start) {
            if (used[start]) return;
            used[start] = 1;
            for (auto &u : g.g[start].e)
                get_euler(u);
            euler.push_back(start);
        }

        void coloring(int start, int color) {
            if (res.colors[start] != -1) return;
            res.colors[start] = color;
            for (auto &u : invg.g[start].e)
                coloring(u, color);
        }

        condensation condense() {
            for (int i = 0; i < g.n; i++)
                if (!used[i])
                    get_euler(i);
            int color = 0;
            for (int i = g.n - 1; i >= 0; i--)
                if (res.colors[euler[i]] == -1)
                    coloring(euler[i], color++);
            res.condensed.n = color;
            res.condensed.g = new node[color];
            for (int v = 0; v < g.n; v++)
                for (int i = 0; i < 26; i++)
                    for (auto &u : g.g[v].l[i])
                        res.condensed.g[res.colors[v]].l[i].push_back(res.colors[u]);
            for (int v = 0; v < color; v++) {
                for (int i = 0; i < 26; i++) {
                    sort(all(res.condensed.g[v].l[i]));
                    res.condensed.g[v].l[i].erase(unique(all(res.condensed.g[v].l[i])), res.condensed.g[v].l[i].end());
                }
            }
            for (int v = 0; v < g.n; v++)
                for (auto &u : g.g[v].e)
                    if (res.colors[v] != res.colors[u])
                        res.condensed.g[res.colors[v]].e.push_back(res.colors[u]);
            for (int v = 0; v < color; v++) {
                sort(all(res.condensed.g[v].e));
                res.condensed.g[v].e.erase(unique(all(res.condensed.g[v].e)), res.condensed.g[v].e.end());
            }
            return res;
        }
    };
};

void topsort(graph::graph g, int v, vector<int> &res) {
    if(_used[v]) return;
    _used[v] = 1;
    for (auto &j : g.g[v].e)
        topsort(g, j, res);
    res.push_back(v);
}

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0), cout.tie(0);

    freopen("expression.in", "r", stdin);
    freopen("expression.out", "w", stdout);


    string s, t;
    cin >> s >> t;
    parser::parser parser(s);
    dfa::dfa *d = dfa::build_dfa(parser.parse());

    graph::graph g = graph::dfa_to_graph(d);

    graph::condensator cond(g);
    graph::condensator::condensation condensed = cond.condense();
    vector<int> colors = condensed.colors;
    graph::graph condg = condensed.condensed;

    graph::graph condginv = graph::inverse(condg);
    graph::distres dstart = graph::dist(colors[d->start->id], condg);
    graph::distres dfinish = graph::dist(colors[d->finish->id], condginv);


    vector<int> _topsort;
    for(int i = 0; i < condg.n; i++)
        if(!_used[i])
            topsort(condg, i, _topsort);
        
    for (int i = 0; i < condg.n; i++) {
        dp[0][i] = dp[1][i] = dfinish.dist[i];
        dplink[0][i] = dplink[1][i] = i;
    }
    for (int len = 1; len <= t.size(); len++) {
        for (int i = 0; i < condg.n; i++)
            dp[1][i] = INF;
        for (auto &i : _topsort) {
            for (auto &j : condg.g[i].l[t[t.size() - len] - 'a']) {
                if (dp[0][j] + 1 < dp[1][i]) {
                    dp[1][i] = dp[0][j] + 1;
                    dplink[1][i] = dplink[0][j];
                }
            }
            for (auto &j : condg.g[i].e) {
                if (dp[1][j] < dp[1][i]) {
                    dp[1][i] = dp[1][j];
                    dplink[1][i] = dplink[1][j];
                }
            }
        }
        for (int i = 0; i < condg.n; i++) {
            dp[0][i] = dp[1][i];
            dplink[0][i] = dplink[1][i];
        }
    }

    int ans = INF, start = -1;
    for (int v = 0; v < condg.n; v++) {
        if (dstart.dist[v] + dp[1][v] < ans) {
            ans = dstart.dist[v] + dp[1][v];
            start = v;
        }
    }

    if (start == -1)
        cout << "NO";
    else {
        string res = "";

        for (int i = start; i != colors[d->start->id]; i = dstart.pred[i].first)
            if (dstart.pred[i].second != '#')
                res.push_back(dstart.pred[i].second);
        reverse(all(res));

        res += t;
        start = dplink[1][start];

        for (int i = start; i != colors[d->finish->id]; i = dfinish.pred[i].first)
            if (dfinish.pred[i].second != '#')
                res.push_back(dfinish.pred[i].second);

        cout << res;
    }
    return 0;
}
