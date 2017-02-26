#include <iostream>
#include <vector>
#include <list>

using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0


struct action {
    int id;
    bool is_lit;

    action(int id, bool is_lit) {
        this->id = id;
        this->is_lit = is_lit;
    }
};
vector<action> modelStack;


typedef pair<int, int> var_info;

void setLiteralToTrue(int lit);
void disableClause(const var_info& v);
void enableClause(const var_info& v);
int currentValueInModel(int lit);

struct clause {

    vector<var_info> literals;

    void add_literal(int literal, int pos) {
        literals.push_back(var_info(literal, pos));
    }

    bool propagate(int clauseID, bool lit_true) {
        if(lit_true) {
            return false;
            bool disabled_some = false;
            for(int i = 0; i < literals.size(); ++i) {
                int val = currentValueInModel(literals[i].first);
                if(val == UNDEF) {
                    if(not disabled_some) {
                        modelStack.push_back(action(clauseID, false));
                    }
                    disableClause(literals[i]);
                    disabled_some = true;
                }
            }
        } else {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for(int i = 0; not someLitTrue and i < literals.size(); ++i) {
                int val = currentValueInModel(literals[i].first);
                if(val == TRUE) {
                    someLitTrue = true;
                } else if(val == UNDEF) {
                    ++numUndefs;
                    lastLitUndef = literals[i].first;
                }
            }
            if(not someLitTrue and numUndefs == 0) {
                return true;
            } else if(not someLitTrue and numUndefs == 1) {
                setLiteralToTrue(lastLitUndef);
            }
        }
        return false;
    }

    bool check() {
        bool someTrue = false;
        for(int i = 0; not someTrue and i < literals.size(); ++i) {
            someTrue = (currentValueInModel(literals[i].first) == TRUE);
        }
        return someTrue;
    }

    void rollback() {
        for(int i = 0; i < literals.size(); ++i) {
            if(currentValueInModel(literals[i].first) == UNDEF) {
                enableClause(literals[i]);
            }
        }
    }

    void print(int id) {
        cout << "ClauseID = " << id << " with vars: ";
        for(int i = 0; i < literals.size(); ++i) {
            cout << literals[i].first << " ";
        }
        cout << endl;
    }
};

uint numVars;
uint numClauses;
vector<clause> clauses;

typedef pair<int, bool> clause_info;

struct var {
    int value;
    vector<clause_info> true_clauses;
    vector<clause_info> false_clauses;
    short true_size;
    short false_size;

    var() {
        value = UNDEF;
        true_size = 0;
        false_size = 0;
    }

    int add_clause(int id, bool negation) {
        if(negation) {
            false_clauses.push_back(clause_info(id, true));
            ++false_size;
            return false_clauses.size()-1;
        } else {
            true_clauses.push_back(clause_info(id, true));
            ++true_size;
            return true_clauses.size()-1;
        }
    }

    void disable_clause(int lit, int pos) {
        if(lit < 0) {
            if(false_clauses[pos].second) {
                false_clauses[pos].second = false;
                --false_size;
                if(false_size == 0) {
                    setLiteralToTrue(-lit);
                }
            }
        } else {
            if(true_clauses[pos].second) {
                true_clauses[pos].second = false;
                --true_size;
                if(true_size == 0) {
                    setLiteralToTrue(-lit);
                }
            }
        }
    }

    void enable_clause(bool negation, int pos) {
        if(negation) {
            if(not false_clauses[pos].second) {
                false_clauses[pos].second = true;
                ++false_size;
            }
        } else {
            if(not true_clauses[pos].second) {
                true_clauses[pos].second = true;
                ++true_size;
            }
        }
    }

    bool propagate() {
        for(int i = 0, total = 0; i < true_clauses.size() && total < true_size; ++i) {
            clause_info c = true_clauses[i];
            if(c.second) {
                ++total;
                if(clauses[c.first].propagate(c.first, value == TRUE)) {
                    return true;
                }
            }
        }
        for(int i = 0, total = 0; i < false_clauses.size() && total < false_size; ++i) {
            clause_info c = false_clauses[i];
            if(c.second) {
                ++total;
                if(clauses[c.first].propagate(c.first, value == FALSE)) {
                    return true;
                }
            }
        }
        return false;
    }

    bool check_pure(int id) {
        if(false_clauses.size() == 0) {
            setLiteralToTrue(id);
            return true;
        } else if(true_clauses.size() == 0) {
            setLiteralToTrue(-id);
            return true;
        }
        return false;
    }

    int size() {
        return true_size + false_size;
    }
};

vector<var> model;

uint indexOfNextLitToPropagate;
uint decisionLevel;

void readClauses() {
    // Skip comments
    char c = cin.get();
    while(c == 'c') {
        while(c != '\n') {
            c = cin.get();
        }
        c = cin.get();
    }
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    model.resize(numVars + 1, var());
    clauses.resize(numClauses);
    // Read clauses
    for(uint id = 0; id < numClauses; ++id) {
        int lit;
        while(cin >> lit and lit != 0) {
            int pos;
            if(lit < 0) {
                pos = model[-lit].add_clause(id, true);
            } else {
                pos = model[lit].add_clause(id, false);
            }
            clauses[id].add_literal(lit, pos);
        }
    }
}


int currentValueInModel(int lit) {
    if(lit >= 0) {
        return model[lit].value;
    } else {
        if(model[-lit].value == UNDEF) {
            return UNDEF;
        } else {
            return 1 - model[-lit].value;
        }
    }
}


void setLiteralToTrue(int lit) {
    modelStack.push_back(action(lit, true));
    if(lit > 0) {
        model[lit].value = TRUE;
    } else {
        model[-lit].value = FALSE;
    }
}

void disableClause(const var_info& v) {
    model[abs(v.first)].disable_clause(v.first, v.second);
}

void enableClause(const var_info& v) {
    model[abs(v.first)].enable_clause(v.first < 0, v.second);
}

bool propagateGivesConflict() {
    while(indexOfNextLitToPropagate < modelStack.size()) {
        action a = modelStack[indexOfNextLitToPropagate++];
        if(a.is_lit) {
            int lit = a.id;
            if(model[abs(lit)].propagate()) {
                return true;
            }
        }
    }
    return false;
}



int countActiveClauses() {
    int total = 0;
    for(int i = 0; i < model.size(); ++i) {
        total += model[i].true_size;
        total += model[i].false_size;
    }
    return total;
}



void backtrack() {
    uint i = modelStack.size() - 1;
    int lit = 0;
    while(!modelStack[i].is_lit || modelStack[i].id != 0) { // 0 is the DL mark
        action a = modelStack[i];
        if(a.is_lit) {
            lit = a.id;
            model[abs(lit)].value = UNDEF;
        } else {
            clauses[a.id].rollback();
        }
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic forfinding the next decision literal:
int getNextDecisionLiteral() {
    int max = -1;
    int var = 0;
    for(uint i = 1; i <= numVars; ++i) {
        if(model[i].value == UNDEF) {
            if(model[i].size() > max) {
                var = i;
                max = model[i].size();
            }
        }
    }
    return var; // returns 0 when all literals are defined
}

void checkmodel() {
    for(int i = 0; i < numClauses; ++i) {
        if(not clauses[i].check()) {
            cout << "Error in model, clause is not satisfied:";
            clauses[i].print(i);
            exit(1);
        }
    }
}

int main(int argc, char* argv[]) {

    if(argc > 1) {
        freopen(argv[1], "r", stdin);
    } else {
        exit(0);
    }

    readClauses(); // reads numVars, numClauses and clauses
    indexOfNextLitToPropagate = 0;
    decisionLevel = 0;

    // Take care of initial unit clauses, if any
    for(uint i = 0; i < numClauses; ++i) {
        if(clauses[i].literals.size() == 1) {
            int lit = clauses[i].literals.front().first;
            int val = currentValueInModel(lit);
            if(val == FALSE) {
                //cout << "UNSATISFIABLE" << endl;
                return 10;
            } else if(val == UNDEF) {
                setLiteralToTrue(lit);
            }
        }
    }

    for(int i = 1; i < model.size(); ++i) {
        model[i].check_pure(i);
    }

    // DPLL algorithm
    while(true) {
        while(propagateGivesConflict()) {
            if(decisionLevel == 0) {
                //cout << "UNSATISFIABLE" << endl;
                return 10;
            }
            backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if(decisionLit == 0) {
            checkmodel();
            //cout << "SATISFIABLE" << endl;
            return 20;
        }
        // start new decision level:
        modelStack.push_back(action(0, true));  // push mark indicating new DL
        ++indexOfNextLitToPropagate;
        ++decisionLevel;
        setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
    }
}

/*
 * Unit literal search
 * Unit literal propagation
 * Unit literal elimination
 *
 * Pure literal search
 * Pure literal propagation
 * Pure literal elimination
 *
 * Clauses size sorting (?)
 *
 * List of clauses in which a literal appears to speed up the propagation and clauses elimination
 *
 *
 * Use of variable apparition amount to select the higher value as heuristic to speed up the process
 * --------------
 * Cuando a una variable se le cambia su valor:
 *      En los sitios en los que aparezca falso, se podrá propagar una variable indefinida si es la unica que aparece y no hay cierta en la clausula
 *      En los sitios en los que aparezca cierto, se podrá "eliminar" esa cláusula
 */