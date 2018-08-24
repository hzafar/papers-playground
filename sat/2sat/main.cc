#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <stack>
#include <tuple>
#include <vector>

#include "../misc/parseClauses.h"

using namespace std;

void findSCCs(int numEdges, vector<set<int>> const& graph, vector<set<int>>& sccs) {
    int n = 0;
    vector<int> order(numEdges, -1);
    vector<int> link(numEdges, -1);
    vector<bool> onStack(numEdges, false);
    stack<int> S;

    function<void(int)> strongConnect =
        [&n, &order, &link, &onStack, &S, &graph, &sccs, &strongConnect](int vertex)
    {
        order[vertex] = ++n;
        link[vertex] = order[vertex];
        S.push(vertex);
        onStack[vertex] = true;

        for (auto& neighbour : graph[vertex]) {
            if (order[neighbour] < 0) {
                strongConnect(neighbour);
                link[vertex] = min(link[vertex], link[neighbour]);
            } else if (onStack[neighbour]) {
                link[vertex] = min(link[vertex], order[neighbour]);
            }
        }

        if (link[vertex] == order[vertex]) {
            set<int> scc;
            while (true) {
                int v = S.top();
                scc.insert(v);
                S.pop();
                onStack[v] = false;
                if (v == vertex) break;
            }
            sccs.push_back(scc);
        }
    };

    for (int i = 0; i < numEdges; i++) {
        if (order[i] < 0) strongConnect(i);
    }
}

int main(void) {
    vector<vector<int>> clauses;
    map<string, int> varMapping;

    parseClauses(clauses, varMapping);
    int numLiterals = 2 * varMapping.size();

    vector<set<int>> graph(numLiterals, set<int>());
    for (auto& c : clauses) {
        graph[c[0]^1].insert(c[1]);
        graph[c[1]^1].insert(c[0]);
    }

    vector<set<int>> sccs;
    findSCCs(numLiterals, graph, sccs);

    for (auto const& scc : sccs) {
        for (auto it = scc.cbegin(); it != scc.cend();) {
            int v1 = (*it++)>>1;
            if (it != scc.cend() && (*it)>>1 == v1) {
                cout << "~" << endl;
                return 0;
            }
        }
    }

    map<int, bool> assignments;
    for (auto const& scc : sccs) {
        for (auto const& v : scc) {
            assignments.try_emplace(v>>1, (bool)!(v&1));
        }
    }

    for (auto const& p : varMapping) {
        cout << (assignments[p.second] ? "" : "~") << p.first << " ";
    }
    cout << endl;

    return 0;
}
