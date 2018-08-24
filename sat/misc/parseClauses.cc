#include "parseClauses.h"

using namespace std;

bool isComment(string l) {
    return !l[0] || (l[0] == '~' && (l[1] == 32 || !l[1]));
}

void parseClauses(vector<vector<int>>& clauses, map<string, int>& vars) {
    int varNum = 0;
    string l;

    while (getline(cin, l)) {
        if (isComment(l)) continue;

        istringstream clause(l);
        vector<int> newClause;

        for (string var; getline(clause, var, ' ');) {
            int negate = 0;
            if (var[0] == '~') negate = 1, var = var.substr(1);
            if (vars.count(var) == 0) vars.insert(pair<string, int>(var, varNum++));

            newClause.push_back(2 * vars[var] + negate);
        }

        clauses.push_back(newClause);
    }
}
