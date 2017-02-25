#include <iostream>
#include <vector>
#include <list>

using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

enum change_type {
    VALUE_CHANGE, CLAUSE_ELIMINATION
};

struct change {
    change_type type;
    int lit;
    int clauseID = -1;

    change(int lit) {
        type = VALUE_CHANGE;
        this->lit = lit;
    }

    change(int varID, int clauseID, bool negation) {
        type = CLAUSE_ELIMINATION;
        this->lit = negation ? -varID : varID;
        this->clauseID = clauseID;
    }
};

vector<change> modelStack;

void setLiteralToTrue(int lit);
int currentValueInModel(int lit);
void propagateByClause(int lit, int clauseID);

struct clause {

    list<int> literals;
    vector<int> test;

    void add_literal(int literal) {
        literals.push_back(literal);
        test.push_back(literal);
    }

    bool propagate(int clauseID, bool lit_true) {
        if(lit_true) {
            for(auto it = literals.begin(); it != literals.end(); ++it) {
                int val = currentValueInModel(*it);
                if(val == UNDEF) {
                    propagateByClause(*it, clauseID);
                }
            }
        } else {
            bool someLitTrue = false;
            int numUndefs = 0;
            int lastLitUndef = 0;
            for(auto it = literals.begin(); not someLitTrue and it != literals.end(); ++it) {
                int val = currentValueInModel(*it);
                if(val == TRUE) {
                    someLitTrue = true;
                } else if(val == UNDEF) {
                    ++numUndefs;
                    lastLitUndef = *it;
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
        for(auto it = literals.begin(); not someTrue and it != literals.end(); ++it) {
            someTrue = (currentValueInModel(*it) == TRUE);
        }
        return someTrue;
    }

    void print(int id) {
        cout << "ClauseID = " << id << " with vars: ";
        for(auto it = literals.begin(); it != literals.end(); ++it) {
            cout << *it << " ";
        }
        cout << endl;
    }
};

uint numVars;
uint numClauses;
vector<clause> clauses;

struct var {
    int value;
    list<int> true_clauses;
    list<int> false_clauses;

    var() {
        value = UNDEF;
    }

    void add_clause(int id, bool negation) {
        if(negation) {
            false_clauses.push_back(id);
        } else {
            true_clauses.push_back(id);
        }
    }

    void enable_clause(int id, bool negation) {
        if(negation) {
            false_clauses.remove(id);
            false_clauses.push_back(id);
        } else {
            true_clauses.remove(id);
            true_clauses.push_back(id);
        }
    }

    void disable_clause(int varID, int clauseID, bool negation) {
        if(negation) {
            false_clauses.remove(clauseID);
            if(false_clauses.size() == 0) {
                value = TRUE;
                modelStack.push_back(change(varID));
            }
        } else {
            true_clauses.remove(clauseID);
            if(true_clauses.size() == 0) {
                value = FALSE;
                modelStack.push_back(change(varID));
            }
        }
    }

    bool propagate() {
        list<int>::iterator it;
        list<int>::iterator end;
        it = true_clauses.begin();
        end = true_clauses.end();
        while(it != end) {
            if(clauses[*it].propagate(*it, value == TRUE)) {
                return true;
            }
            ++it;
        }
        it = false_clauses.begin();
        end = false_clauses.end();
        while(it != end) {
            if(clauses[*it].propagate(*it, value == FALSE)) {
                return true;
            }
            ++it;
        }
        return false;
    }

    void rollback() {

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
            clauses[id].add_literal(lit);
            if(lit < 0) {
                model[-lit].add_clause(id, true);
            } else {
                model[lit].add_clause(id, false);
            }
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
    modelStack.push_back(change(lit));
    if(lit > 0) {
        model[lit].value = TRUE;
    } else {
        model[-lit].value = FALSE;
    }
}

void propagateByClause(int lit, int clauseID) {
    modelStack.push_back(change(abs(lit), clauseID, lit < 0));
    model[abs(lit)].disable_clause(lit, clauseID, lit < 0);
}


bool propagateGivesConflict() {
    while(indexOfNextLitToPropagate < modelStack.size()) {
        change c = modelStack[indexOfNextLitToPropagate++];
        if(c.type == VALUE_CHANGE) {
            if(model[abs(c.lit)].propagate()) {
                return true;
            }
        }
    }
    return false;
}

void backtrack() {
    uint i = modelStack.size() - 1;
    int lit = 0;
    while(modelStack[i].lit != 0) { // 0 is the DL mark
        change c = modelStack[i];
        lit = c.lit;
        if(c.type == VALUE_CHANGE) {
            model[abs(lit)].value = UNDEF;
        } else {
            model[abs(lit)].enable_clause(c.clauseID, lit < 0);
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
    for(uint i = 1; i <= numVars; ++i) {// stupid heuristic:
        if(model[i].value == UNDEF) { // returns first UNDEF var, positively
            return i;
        }
    }
    return 0; // returns 0 when all literals are defined
}

void checkmodel() {
    for(int i = 0; i < numClauses; ++i) {
        if(not clauses[i].check()) {
            cout << "Error in model, clause is not satisfied:";
            clauses[i].print(i);
            cout << "decissionLevel = " << decisionLevel << endl;
            exit(1);
        }
    }
}



int max_level = 0;

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
            int lit = clauses[i].literals.front();
            int val = currentValueInModel(lit);
            if(val == FALSE) {
                //cout << "UNSATISFIABLE" << endl;
                return 10;
            } else if(val == UNDEF) {
                setLiteralToTrue(lit);
            }
        }
    }
    // DPLL algorithm
    while(true) {
        while(propagateGivesConflict()) {
            if(modelStack.size() > max_level) {
                max_level = modelStack.size();
            }
            if(decisionLevel == 0) {
                //cout << "UNSATISFIABLE" << endl;
                cout << "Max level = " << max_level << endl;
                return 10;
            }
            backtrack();
        }
        int decisionLit = getNextDecisionLiteral();
        if(decisionLit == 0) {
            checkmodel();
            //cout << "SATISFIABLE" << endl;
            cout << "Max level = " << max_level << endl;
            return 20;
        }
        // start new decision level:
        modelStack.push_back(change(0));  // push mark indicating new DL
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