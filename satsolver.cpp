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
void registerConflict(int lit);
int totalConflicts = 1;

struct clause {

    vector<var_info> literals;

    void add_literal(int literal, int pos) {
        literals.push_back(var_info(literal, pos));
    }

    bool propagate(int clauseID, bool lit_true) {
        if(lit_true) {
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
                for(int i = 0; i < literals.size(); ++i) {
                    registerConflict(literals[i].first);
                }
                totalConflicts += literals.size();
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

    int getUndefs() {
        int numUndefs = 0;
        for(int i = 0; i < literals.size(); ++i) {
            int val = currentValueInModel(literals[i].first);
            if(val == UNDEF) {
                ++numUndefs;
            }
        }
        return numUndefs;
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

struct clause_info {
    int id;
    bool active;
    int next;
    int prev;

    clause_info(int id, bool active, int prev, int next) {
        this->id = id;
        this->active = active;
        this->next = next;
        this->prev = prev;
    }
};

struct var {
    int value;
    vector<clause_info> true_clauses;
    vector<clause_info> false_clauses;
    int true_size;
    int false_size;
    int first_true;
    int first_false;
    float true_conflicts;
    float false_conflicts;

    int next;
    int prev;

    var() {
        value = UNDEF;
        true_size = 0;
        false_size = 0;
        first_true = -1;
        first_false = -1;
        true_conflicts = 0;
        false_conflicts = 0;
    }

    int i_add_clause(vector<clause_info>& clauses, int& first, int& size, int newID) {
        clauses.push_back(clause_info(newID, true, size-1, -1));
        ++size;
        if(size > 1) {
            clauses[size-2].next = size-1;
        } else {
            first = 0;
        }
        return size-1;
    }

    int add_clause(int id, bool negation) {
        if(negation) {
            return i_add_clause(false_clauses, first_false, false_size, id);
        } else {
            return i_add_clause(true_clauses, first_true, true_size, id);
        }
    }

    void i_disable_clause(vector<clause_info>& clauses, int pos, int& first, int& size) {
        if(clauses[pos].active) {
            clauses[pos].active = false;
            --size;
            int prev = clauses[pos].prev;
            int next = clauses[pos].next;
            if(prev != -1) {
                clauses[prev].next = next;
            }
            if(next != -1) {
                clauses[next].prev = prev;
            }
            if(first == pos) {
                first = next;
            }
        }
    }

    void disable_clause(int lit, int pos) {
        if(lit < 0) {
            i_disable_clause(false_clauses, pos, first_false, false_size);
            if(false_size == 0) {
                setLiteralToTrue(-lit);
            }
        } else {
            i_disable_clause(true_clauses, pos, first_true, true_size);
            if(true_size == 0) {
                setLiteralToTrue(-lit);
            }
        }
    }

    void i_enable_clause(vector<clause_info>& clauses, int pos, int& first, int& size) {
        if(not clauses[pos].active) {
            if(first > pos) {
                clauses[pos].prev = -1;
                clauses[pos].next = first;
                clauses[first].prev = pos;
                first = pos;
            } else if(first == -1) {
                first = pos;
                clauses[pos].prev = -1;
                clauses[pos].next = -1;
            } else {
                int k = pos-1;
                while(not clauses[k].active) {
                    --k;
                }
                clauses[pos].prev = k;
                clauses[pos].next = clauses[k].next;
                clauses[k].next = pos;
                if(clauses[pos].next != -1) {
                    clauses[clauses[pos].next].prev = pos;
                }
            }
            clauses[pos].active = true;
            ++size;
        }
    }

    void enable_clause(bool negation, int pos) {
        if(negation) {
            i_enable_clause(false_clauses, pos, first_false, false_size);
        } else {
            i_enable_clause(true_clauses, pos, first_true, true_size);
        }
    }

    bool propagate() {
        int i = first_true;
        while(i != -1) {
            clause_info c = true_clauses[i];
            if(clauses[c.id].propagate(c.id, value == TRUE)) {
                return true;
            }
            i = true_clauses[i].next;
        }
        i = first_false;
        while(i != -1) {
            clause_info c = false_clauses[i];
            if(clauses[c.id].propagate(c.id, value == FALSE)) {
                return true;
            }
            i = false_clauses[i].next;
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

    int i_size(vector<clause_info>& var_clauses, int real_size, int first) {
        int size = 0;
        int i = first;
        while(i != -1) {
            clause_info c = var_clauses[i];
            int numUndefs = clauses[c.id].getUndefs();
            size += numUndefs == 2 ? 1 : 0;
            i = var_clauses[i].next;
        }
        return size;
    }

    //Used by the heuristic
    float weight(bool sizeOfTrueClauses) {
        if(sizeOfTrueClauses) {
            return i_size(true_clauses, true_size, first_true)*(true_conflicts/totalConflicts);
        } else {
            return i_size(false_clauses, false_size, first_false)*(false_conflicts/totalConflicts);
        }
    }

    void addConflict(bool negation) {
        if(negation) {
            ++true_conflicts;
        } else {
            ++false_conflicts;
        }
    }
};

vector<var> model;
int first_undef;
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
    for(int i = 1; i < model.size(); ++i) {
        model[i].prev = i-1;
        model[i].next = i+1;
    }
    first_undef = 1;
    model[model.size()-1].next = 0;

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
    int var = abs(lit);
    int prev = model[var].prev;
    int next = model[var].next;
    if(prev != 0) {
        model[prev].next = next;
    }
    if(next != 0) {
        model[next].prev = prev;
    }
    if(first_undef == var) {
        first_undef = next;
    }
}

void setLiteralToUndef(int lit) {
    int var = abs(lit);
    model[var].value = UNDEF;
    if(first_undef > var) {
        model[var].prev = 0;
        model[var].next = first_undef;
        model[first_undef].prev = var;
        first_undef = var;
    } else if(first_undef == 0) {
        first_undef = var;
        model[var].prev = 0;
        model[var].next = 0;
    } else {
        int k = var-1;
        while(k > 0 && model[k].value != UNDEF) {
            --k;
        }
        model[var].prev = k;
        model[var].next = model[k].next;
        model[k].next = var;
        if(model[var].next != 0) {
            model[model[var].next].prev = var;
        }
    }
}

void disableClause(const var_info& v) {
    model[abs(v.first)].disable_clause(v.first, v.second);
}

void enableClause(const var_info& v) {
    model[abs(v.first)].enable_clause(v.first < 0, v.second);
}

void registerConflict(int lit) {
    model[abs(lit)].addConflict(lit < 0);
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

void backtrack() {
    uint i = modelStack.size() - 1;
    int lit = 0;
    while(!modelStack[i].is_lit || modelStack[i].id != 0) { // 0 is the DL mark
        action a = modelStack[i];
        if(a.is_lit) {
            lit = a.id;
            setLiteralToUndef(lit);
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


int getNextDecisionLiteral() {
    float maxWeight = -1;
    int lit = 0;
    int i = first_undef;
    while(i != 0) {
        float true_size = model[i].weight(true);
        float false_size = model[i].weight(false);
        float weight = true_size + false_size;
        if(weight > maxWeight) {
            maxWeight = weight;
            lit = true_size > false_size ? i : -i;
        }
        i = model[i].next;
    }
    return lit; // returns 0 when all literals are defined
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
 * Done - Unit literal search
 * Done - Unit literal propagation
 * Done - Unit literal elimination
 *
 * Done - Pure literal search
 * Done - Pure literal propagation
 * Done - Pure literal elimination
 *
 * Discarded - Clauses size sorting (?)
 *
 * Done - List of clauses in which a literal appears to speed up the propagation and clauses elimination
 *
 *
 * Done & improved - Use of variable apparition amount to select the higher value as heuristic to speed up the process
 * --------------
 * Cuando a una variable se le cambia su valor:
 * Done - En los sitios en los que aparezca falso, se podrá propagar una variable indefinida si es la unica que aparece y no hay cierta en la clausula
 * Done - En los sitios en los que aparezca cierto, se podrá "eliminar" esa cláusula
 
 * Done - List over vector on clauses' vars
 * Done - List over vector on model (for undefined vars)
 *
 * TODO - Try to save the linear traverse over clausules in each var to compute it's heuristic (weight)
 * TODO - Use unordered map instead of list for choosing next literal
 * TODO - Alternative to ^. Use list and remove when var is not undefined.
 *
 * TODO - USE A HEAP TO GET THE MOST CONFLICTIVE VAR (or vars). Counting only
 */
