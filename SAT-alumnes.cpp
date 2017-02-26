#include <iostream>
#include <vector>
#include <list>

using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

void setLiteralToTrue(int lit);
void setVarToPossiblePure(int var);
int currentValueInModel(int lit);

struct clause {

    list<int> literals;

    void add_literal(int literal) {
        literals.push_back(literal);
    }

    bool propagate(int clauseID, bool lit_true) {
        if(lit_true) {
            return false;
            for(auto it = literals.begin(); it != literals.end(); ++it) {
                int val = currentValueInModel(*it);
                if(val == UNDEF) {
                    setVarToPossiblePure(abs(*it));
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
    bool possible_pure;
    bool positive_pure;

    var() {
        value = UNDEF;
        possible_pure = false;
    }

    void add_clause(int id, bool negation) {
        if(negation) {
            false_clauses.push_back(id);
        } else {
            true_clauses.push_back(id);
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

    bool is_initially_pure() {
        if(false_clauses.size() == 0) {
            positive_pure = false;
            return true;
        } else if(true_clauses.size() == 0) {
            positive_pure = true;
            return true;
        }
        return false;
    }

    bool is_pure() {
        auto it = true_clauses.begin();
        auto end = true_clauses.end();
        while(it != end) {
            if(not clauses[*it].check()) {
                break;
            }
            ++it;
        }
        if(it == end) {
            positive_pure = true;
            return true;
        } else {
            it = false_clauses.begin();
            end = false_clauses.end();
            while(it != end) {
                if(not clauses[*it].check()) {
                    possible_pure = false;
                    return false;
                }
                ++it;
            }
            positive_pure = false;
            return true;
        }
    }

    int size() {
        return true_clauses.size() + false_clauses.size();
    }
};

vector<var> model;
vector<int> modelStack;
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
    modelStack.push_back(lit);
    if(lit > 0) {
        model[lit].value = TRUE;
    } else {
        model[-lit].value = FALSE;
    }
}


void setVarToPossiblePure(int varID) {
    model[varID].possible_pure = true;
}


bool propagateGivesConflict() {
    while(indexOfNextLitToPropagate <= modelStack.size()) {
        if(indexOfNextLitToPropagate == modelStack.size()) {
            for(int i = 1; i < model.size(); ++i) {
                if(model[i].value == UNDEF && model[i].possible_pure) {
                    if(model[i].is_pure()) {
                        setLiteralToTrue(model[i].positive_pure ? -i: i);
                        model[i].possible_pure = false;
                    }
                }
            }
            if(indexOfNextLitToPropagate == modelStack.size()) {
                break;
            }
        } else {
            int lit = modelStack[indexOfNextLitToPropagate++];
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
    while(modelStack[i] != 0) { // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)].value = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
    for(int i = 1; i < model.size(); ++i) {
        model[i].possible_pure = false;
    }
}


// Heuristic forfinding the next decision literal:
int getNextDecisionLiteral() {
    int max = 0;
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

    for(int i = 1; i < model.size(); ++i) {
        if(model[i].is_initially_pure()) {
            model[i].possible_pure = true;
        }
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
        modelStack.push_back(0);  // push mark indicating new DL
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