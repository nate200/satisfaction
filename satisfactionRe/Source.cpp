#include<iostream>
#include<stack>
#include<vector>
#include<algorithm>
#include<unordered_map>
#define FOR(i, n) for (size_t i = 0u; i < n; i++)
#define FORS(i, s, n) for (size_t i = s; i < n; i++)
#define FOR1(i, n) for (size_t i = 1u; i < n; i++)
#define VALWNEGATE(valMem, i, expVals) valMem[expVals[i] & 0x7FFFFFFFu] ^ (expVals[i] >> 31)//variable with negation
/*
    expVals[i], 32th-bit = negation flag, 1st-31th bit = variable/expression
    0x7FFFFFFFu = 0111...1111 is used to remove negation flag
*/

using namespace std;

enum boolOperator { AND = 0, OR = 1, NOTHING = 2 }; //replace with integer, can't convert enum to int ;(
struct Expression {//1 boolean operation per 1 expression
    boolOperator oper = boolOperator::NOTHING;

    size_t expIndex, len = 0, *vals = new size_t[0];//0-25=A-Z, 26=true, 27=false, 28-70=an index of an Expression, 32th-bit for negation
    int lv;//highest lv will be calculated first, children have higher lv than their parent
    //vector<size_t> *valsVector = nullptr;
    Expression(boolOperator oper, size_t expIndex, int lv, size_t expInfoIndex):
        oper(oper), expIndex(expIndex), lv(lv), len(expInfoIndex){
    }
    void addValsFromExpInfo(vector<size_t> expInfo_vals, size_t* indexMapper) {
        len = expInfo_vals.size();
        vals = new size_t[len];
        size_t* it_val = vals;

        //valsVector = new vector<size_t>;
        //valsVector->reserve(len);

        for (const size_t val : expInfo_vals) {
            *it_val = indexMapper[val & 0x7FFFFFFFu] | val & 0x80000000;
            //valsVector->push_back(*it_val);
            it_val++;
        }
    }
    ~Expression() { delete[] vals; /*delete valsVector;*/ }
};
static struct ExpressionBuilder {
    ExpressionBuilder() { throw ""; }

    struct ExpressionInfo {//1 boolean operation per 1 expression
        boolOperator oper = boolOperator::NOTHING;

        size_t expIndex;
        vector<size_t> vals;//not sorted: 0-25=A-Z, 26=true, 27=false, 28-70=an index of an Expression, 32th-bit for negation
        int lv;//highest lv will be calculated first, children have higher lv than their parent

        pair<char, int> valFound;

        ExpressionInfo* baseLine = nullptr, * holdingChild = nullptr;//vector won't reallocate because of reserve(96);
        size_t foundNegate = 0;

        ExpressionInfo(boolOperator oper, size_t expCounter, ExpressionInfo* baseLine = nullptr) : oper(oper), expIndex(expCounter), baseLine(&*baseLine) {}

        static constexpr size_t negate32thBit[2] = { 0u , 0x80000000 };
        
        void addValAny(size_t& newNumBoolFound, size_t* _varFound) {
            if (valFound.second) {//add variable A-Z
                const int index = valFound.first - 65;
                addVal(index);
                newNumBoolFound += !_varFound[index]; // == 0
                _varFound[index] |= 1u;
            }
            else addVal(valFound.first);//add exp
        }
        void addExp() { addVal(valFound.first); }
        void addVal(uint32_t val) {
            vals.push_back(val | negate32thBit[foundNegate]);
            foundNegate = 0;
        }
        void flip_foundNegate() { foundNegate = !foundNegate; }
        void setValFound(char val, int isChar) {
            valFound.first = val;
            valFound.second = isChar;
        }
        void addValFromOR(ExpressionInfo *exp, size_t& newNumBoolFound, size_t* _varFound) {
            valFound.first = exp->valFound.first;
            valFound.second = exp->valFound.second;
            foundNegate = exp->foundNegate;
            addValAny(newNumBoolFound, _varFound);// A|B&C, A|~()&C
        }
        void takeOverExp(ExpressionInfo* exp, size_t& newNumBoolFound, size_t* _varFound) {
            valFound.first = exp->valFound.first;
            valFound.second = exp->valFound.second;
            foundNegate ^= exp->foundNegate;//B&~(~((~(A))))
            holdingChild = nullptr;
            //addValAny(newNumBoolFound, _varFound); removed to fix a bug: B&((((A))))
        }
        void addAllValsFromChild(ExpressionInfo* exp) {
            const size_t fn = negate32thBit[foundNegate];
            foundNegate = 0;
            for (const size_t val : exp->vals)
                vals.push_back(val | fn);
        }
        ~ExpressionInfo() { }
    };

    static void stringToExp(vector<Expression>& retExp, const char* exp, size_t& newNumBoolFound, size_t* varFound) {

        vector<ExpressionInfo> expInfos;
        expInfos.reserve(70);//prevent reallocation which will mess up all the address

        ExpressionInfo* baseLine, * currExp;
        expInfos.emplace_back(boolOperator::NOTHING, 27u, nullptr);//baseLine
        baseLine = &expInfos.back();
        expInfos.emplace_back(boolOperator::NOTHING, 28u, baseLine);
        currExp = &expInfos.back();
        baseLine->holdingChild = currExp;

        for (size_t i = 0u; exp[i] != '\0'; i++) {
            //cout << exp[i];
            switch (exp[i]) {
            case '&':
                switch (currExp->oper) {
                case boolOperator::AND:
                    currExp->addValAny(newNumBoolFound, varFound);
                    break;
                case boolOperator::OR:
                    add_ANDexp_to_ORcurr(expInfos, currExp, newNumBoolFound, varFound);
                    break;
                case boolOperator::NOTHING:
                    currExp->addValAny(newNumBoolFound, varFound);
                    currExp->oper = boolOperator::AND;
                    break;
                }
                break;
            case '|':
                currExp->addValAny(newNumBoolFound, varFound);
                switch (currExp->oper) {
                case boolOperator::AND:
                    if (baseLine->holdingChild->oper == boolOperator::OR) {
                        currExp = baseLine->holdingChild;//go back to OR
                        currExp->addExp();
                    }
                    else add_ORexp_with_ANDcurr(expInfos, baseLine, currExp, newNumBoolFound, varFound);
                    break;
                case boolOperator::NOTHING:
                    currExp->oper = boolOperator::OR;
                    break;
                }
                break;
            case '~':
                currExp->flip_foundNegate();
                break;
            case '(': {//like normal A-Z, it's a variable with other variables inside
                add_baseLine_to_currExp(expInfos, baseLine, currExp);
                break;
            }
            case ')': {//can't merge child and baseline with the same oper in here, case: A|(B|C)&D
                if (currExp->oper == boolOperator::NOTHING) {
                    baseLine->takeOverExp(currExp, newNumBoolFound, varFound);
                    if (&expInfos.back() == currExp)//A|((A&B|C)) = |,(,&,|
                        expInfos.pop_back();
                }
                else {
                    currExp->addValAny(newNumBoolFound, varFound);
                    if (baseLine->holdingChild != currExp) //D&(A|B&C)
                        baseLine->holdingChild->addValAny(newNumBoolFound, varFound);
                }

                currExp = currExp->baseLine;
                baseLine = currExp->baseLine;
                break;
            }
            default:
                currExp->setValFound(exp[i], 1);//cant add new variable until the next oper sign is known
                break;
            }
        }
        //cout << "\n";
        currExp->addValAny(newNumBoolFound, varFound);
        if (baseLine->holdingChild != currExp) //fix bug: A&B|C&(Z&X)
            baseLine->holdingChild->addValAny(newNumBoolFound, varFound);

        size_t indexMapper[98];//fix bug: oper::NOTHING messes up all the index in vals
        {
            FOR(i, 28u)
                indexMapper[i] = i;
            size_t currIndex = 28u;
            for (const ExpressionInfo& exp_info : expInfos)
                if (exp_info.oper != boolOperator::NOTHING)
                    indexMapper[exp_info.expIndex] = currIndex++;
        }

        retExp.reserve(expInfos.size() - 1);
        walkTreeExp(retExp, expInfos, indexMapper, baseLine->holdingChild, 0);
        
        if (retExp.empty()) {//fix bug "if A then" ;(
            currExp = &expInfos.back();
            retExp.emplace_back(currExp->oper, 28u, 0, 1);
            retExp[0].addValsFromExpInfo(currExp->vals, indexMapper);
        }
        else {
            sort(retExp.begin(), retExp.end(), sortExpressionInfo());
            for (Expression& expp : retExp)//sorting messes up all the addresses of vals
                expp.addValsFromExpInfo(expInfos[expp.len].vals, indexMapper);
        }
    }
    static void walkTreeExp(vector<Expression>& retExp, vector<ExpressionInfo>& expInfos, size_t *indexMapper, ExpressionInfo * currExp, const int lv) {
        //boolOperator oper, size_t expIndex, int lv, size_t expInfoIndex
        if(currExp->oper != boolOperator::NOTHING)
            retExp.emplace_back(currExp->oper, indexMapper[currExp->expIndex], lv, currExp->expIndex - 27u);

        const int nextLv = lv + 1;
        for (const size_t val : currExp->vals) {
            size_t index = val & 0x7FFFFFFFu;
            if (index > 27) 
                walkTreeExp(retExp, expInfos, indexMapper, &expInfos[index - 27u], nextLv);
        }
    }
    struct sortExpressionInfo {
        inline bool operator() (const Expression& exp1, const Expression& exp2) {
            return (exp1.lv > exp2.lv);
        }
    };


    static void add_ORexp_with_ANDcurr(vector<ExpressionInfo>& expInfos, ExpressionInfo*& baseLine, ExpressionInfo*& currExp, size_t& newNumBoolFound, size_t* varFound) {
        expInfos.emplace_back(boolOperator::OR, expInfos.size() + 27u, baseLine);
        ExpressionInfo* newORexp = &expInfos.back();
        newORexp->setValFound(currExp->expIndex, 0u);
        newORexp->addValAny(newNumBoolFound, varFound);// A&B|C

        baseLine->setValFound(newORexp->expIndex,0);//fix bug: B&((((A)&C|D))), forgot to change valFound
        baseLine->holdingChild = newORexp;
        currExp = newORexp;
    }
    static void add_ANDexp_to_ORcurr(vector<ExpressionInfo>& expInfos, ExpressionInfo*& currExp, size_t& newNumBoolFound, size_t* varFound) {
        expInfos.emplace_back(boolOperator::AND, expInfos.size() + 27u, currExp->baseLine);
        ExpressionInfo* newANDexp = &expInfos.back();
        newANDexp->addValFromOR(currExp, newNumBoolFound, varFound);

        currExp->setValFound(newANDexp->expIndex, 0);
        currExp->foundNegate = 0;

        currExp = newANDexp;
    }
    static void add_baseLine_to_currExp(vector<ExpressionInfo>& expInfos, ExpressionInfo*& baseLine, ExpressionInfo*& currExp) {
        expInfos.emplace_back(boolOperator::NOTHING, expInfos.size() + 27u, currExp);
        ExpressionInfo* newExp = &expInfos.back();

        currExp->holdingChild = newExp;
        currExp->setValFound(newExp->expIndex, 0);//~()&A, ()|A, ()

        baseLine = currExp;
        currExp = newExp;
    }
};
struct CondStack {   
    vector<uint32_t> allAns[2];
    //0=else, 1=if; allAns[0].size() + allAns[1].size() <= 2^boolIndexLen
    //new variables fill up from right to left

    uint32_t condState = 1,//0=else, 1=if for allAns
        boolVarIndex[26],//index of boolVarIndex = index of bit in allAns, 0-25=A-Z, +65 to char at checkpoint
        boolIndexLen = 0;

    int finalAns[2][26];//2nd dimension for if-else, ordering is the same as boolVarIndex[26], 0=[val must be false], 1=[val must be true], -1 = both, -2 = unreachable, -3=unknown

    CondStack() {//for static CondStack _dummy_stack;
        FOR(i, 26u) finalAns[0][i] = finalAns[1][i] = -3;
        allAns[0].push_back(0);
        allAns[1].push_back(0);
    }

    CondStack(const char* cond, const CondStack &prev){
        if (prev.finalAns[condState][0] == -2) {//unreachable
            finalAns[0][0] = finalAns[1][0] = -2;
            return;
        }
        FOR(i, 26u) finalAns[0][i] = finalAns[1][i] = -3;
        getStackAns(cond, prev);
    }

    void getStackAns(const char* cond, const CondStack& prev) {
        uint32_t(*boolOperation[3])(uint32_t*, uint32_t, uint32_t*) = {
            { [](uint32_t* expVals, uint32_t expValslen, uint32_t* valMem) { uint32_t ret = VALWNEGATE(valMem,0,expVals); FOR1(i,expValslen) ret &= VALWNEGATE(valMem,i,expVals); return ret; } },
            { [](uint32_t* expVals, uint32_t expValslen, uint32_t* valMem) { uint32_t ret = VALWNEGATE(valMem,0,expVals); FOR1(i,expValslen) ret |= VALWNEGATE(valMem,i,expVals); return ret; } },
            { [](uint32_t* expVals, uint32_t expValslen, uint32_t* valMem) { return VALWNEGATE(valMem,0,expVals); } }
        };

        const size_t prev_boolIndexLen = prev.boolIndexLen;

        size_t allPossBool = 0;
        vector<Expression> exps;
        {
            size_t varFound[26] = { 0u };//bitset: 2=old stack has variable, 1=found, 3=2|1, 0=not found          
            FOR(i, prev_boolIndexLen) {
                varFound[prev.boolVarIndex[i]] = 2u;
                boolVarIndex[i] =  prev.boolVarIndex[i];
            }

            ExpressionBuilder::stringToExp(exps, cond, allPossBool, varFound);

            allPossBool = 1u << allPossBool;//works on case: newNumBoolFound = 0

            boolIndexLen = prev_boolIndexLen;
            FOR(i, 26u) 
                if (varFound[i] == 1u) // 0|1=1, 2|1=3
                    boolVarIndex[boolIndexLen++] = i;
        }

        size_t findValAns[2][26], findValAnsLen[2];
        findValAnsLen[0] = findValAnsLen[1] = boolIndexLen;
        FOR(i, boolIndexLen) findValAns[0][i] = findValAns[1][i] = boolVarIndex[i];

        size_t memVal[75];//array index: [0-25=A-Z], [26=false], [27=true], [28-74=Exps]
        memVal[26] = 0u; memVal[27] = 1u;

        //added to prevent vector reallocation
        uint32_t ansLen = prev.allAns[prev.condState].size() * allPossBool;
        uint32_t* allAnsTemp = new uint32_t[ansLen], *allAnsTempResult = new uint32_t[ansLen];
        uint32_t ansLenEach[2] = { 0,0 };
        ansLen = 0;

        uint32_t* expResult = &memVal[exps.back().expIndex];
        for (uint32_t prevAnsMem : prev.allAns[prev.condState]) {

            FOR(i, prev_boolIndexLen) 
                memVal[boolVarIndex[i]] = prevAnsMem >> i & 1u;

            FOR(i, allPossBool) {
                uint32_t boolmem = prevAnsMem | i << prev_boolIndexLen;
                FORS(j, prev_boolIndexLen, boolIndexLen)
                    memVal[boolVarIndex[j]] = boolmem >> j & 1u;

                for(const Expression &exp : exps)//dereferencing an array of exps is slow, removed by using foreach
                    memVal[exp.expIndex] = boolOperation[exp.oper](exp.vals, exp.len, memVal);

                const uint32_t result = *expResult;

                allAnsTemp[ansLen] = boolmem;
                allAnsTempResult[ansLen] = result;
                ansLen++; ansLenEach[result]++;

                for (size_t j = 0; j < findValAnsLen[result]; j++) {
                    const uint32_t index = findValAns[result][j], currBit = memVal[index];
                    if (finalAns[result][index] == -3)finalAns[result][index] = currBit;
                    else if (finalAns[result][index] != currBit) {
                        findValAnsLen[result]--;
                        findValAns[result][j] = findValAns[result][findValAnsLen[result]];
                        finalAns[result][index] = -1;
                        j--;
                    }
                }
            }
        }
        allAns[0].reserve(ansLenEach[0]);
        allAns[1].reserve(ansLenEach[1]);
        FOR(i, ansLen) allAns[allAnsTempResult[i]].push_back(allAnsTemp[i]);

        if (ansLenEach[0] == 0)finalAns[0][0] = -2;
        else if (ansLenEach[1] == 0)finalAns[1][0] = -2;

        delete[] allAnsTempResult; delete[] allAnsTemp;
    }

    void switchToElse() {
        condState = 0;
        allAns[1].clear();
    }

    void checkpoint() {  
        cout << '>';
        if (finalAns[condState][0] == -2)cout << "unreachable";
        else {
            FOR(i, boolIndexLen)
                if (-1 < finalAns[condState][i])
                    cout << (char)((i + 65) + (32 * !finalAns[condState][i]));//upper = true, lower = false
        }
        cout << "\n";
    }

    ~CondStack() {
        allAns[0].clear(); allAns[1].clear();
    }

};

/*void sss(Expression *&aa) {
    cout << aa << " " << &*aa << "\n";
}*/
int main() {
    /*size_t valss[1];
    Expression aa(boolOperator::NOTHING,0,0, 0, valss);
    cout << &aa << "\n";
    return 0;*/

    ios::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);

    stack<CondStack> ifs;
    ifs.push(CondStack());

    char inputState[11], then[5], cond[130];

    enum Statement {//ascii of the first char(lowercase)
        CHECKPOINT = 0x63,//99 to hex = 63
        ELSE = 0x65,
        FI = 0x66,
        IF = 0x69
    };
    while (cin >> inputState) {
        switch (inputState[0]) {
        case Statement::IF : {//if
            cin >> cond >> then;
            ifs.emplace(cond, ifs.top());
            break;
        }
        case  Statement::ELSE : {//else
            ifs.top().switchToElse();
            break;
        }
        case  Statement::CHECKPOINT : {//checkpoint
            ifs.top().checkpoint();
            break;
        }
        case  Statement::FI ://fi
            ifs.pop();
            break;
        }
    }
    return 0;
}
/*
* allAns stores boolean value that satisfied the previous condition in bits of an int
* boolVarIndex stores each bit position of variable, variable are fix by index of bits
*
* boolVarIndex = [A,B,D,G,M...], boolIndexLen = 9
* allAns[0][0] =
* ...0000000110010101
* ..........ZSRPMGDBA
*
* when the next stack has additional variables, they will be added right next to the previous variable set
* new stack only run all its new possible variable after prev.boolIndexLen
*
* boolVarIndex = [A,B,D,G,M...Y,C,K,J], boolIndexLen = 13
* allAns[0][0] =
* ...0001010110010101
* ......JKCYZSRPMGDBA
*/