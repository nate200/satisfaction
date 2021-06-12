#include<iostream>
#include<stack>
#include<vector>
#include<algorithm>
#define FOR(i, n) for (size_t i = 0u; i < n; i++)
#define FORS(i, s, n) for (size_t i = s; i < n; i++)
#define FOR1(i, n) for (size_t i = 1u; i < n; i++)
#define VALWNEGATE(valMem, i, expVals) valMem[expVals[i] & 0x7FFFFFFFu] ^ (expVals[i] >> 31)//variable with negation
/*
    expVals[i], 32th-bit = negation flag, 1st-31th0bit = variable/index of an expression
    0x7FFFFFFFu = 0111...1111 is used to remove negation flag
*/

using namespace std;

enum boolOperator { AND = 0, OR = 1, NOTHING = 2 }; //replace with integer, can't convert enum to int ;(
struct Expression {//1 boolean operation per 1 expression
    boolOperator oper = boolOperator::NOTHING;

    size_t len = 0, vals[70];//0-25=A-Z, 26=true, 27=false, 28-70=an index of an Expression, 32th-bit for negation
    int lv;//highest lv will be calculated first, children have higher lv than their parent

    pair<char, int> valFound;

    //Expression* parentExp = nullptr; //address will be invalid when a vector relocates itself (when it reaches its capacity).
    size_t parentExpIndex = 0xFFFFFFFF, expIndex, foundNegate = 0, hasNoBracket;

    Expression(int lv, size_t expCounter, size_t hasNoBracket) : lv(lv), expIndex(expCounter), hasNoBracket(hasNoBracket){}

    static constexpr size_t negate32thBit[2] = { 0u , 0x80000000 };
    void addVal(uint32_t val) { 
        vals[len++] = val | negate32thBit[foundNegate];
        foundNegate = 0;
    }
    void flipNegate() { foundNegate = !foundNegate; }
    void setValFound(char val, int isChar) { 
        valFound.first = val;
        valFound.second = isChar;
    }
    void takeOverCurrInfo(Expression& exp) {
        valFound.first = exp.valFound.first;
        valFound.second = exp.valFound.second;
        foundNegate ^= exp.foundNegate;
    }
    ~Expression() {}
};
static struct ExpressionBuilder {
    ExpressionBuilder() { throw ""; }

    static void stringToExp(vector<Expression> &retExp, const char* exp, size_t& newNumBoolFound, size_t* varFound) {
        retExp.emplace_back(0, 28u, 0u);//lowest lv is not 0

        Expression* parentExp = nullptr, * currExp = &retExp.back();

        size_t expStringLen = -1;

        for (size_t i = 0u; exp[i] != '\0'; i++, expStringLen++) {
            //cout << exp[i];
            switch (exp[i]) {
            case '&':
                if (currExp->oper == boolOperator::AND)
                    addValAny(currExp, newNumBoolFound, varFound);
                else if (currExp->oper == boolOperator::OR)
                    do_ORcurr_add_NewANDchild(retExp, currExp, parentExp, newNumBoolFound, varFound);//& has higher priority                
                else {//currExp->oper == boolOperator::NOTHING
                    addValAny(currExp, newNumBoolFound, varFound);
                    currExp->oper = boolOperator::AND;
                }
                break;
            case '|':
                addValAny(currExp, newNumBoolFound, varFound);
                if (currExp->oper == boolOperator::AND) {
                    if (parentExp != nullptr && parentExp->oper == boolOperator::OR) {
                        currExp = &(*parentExp);
                        if (currExp->parentExpIndex != 0xFFFFFFFF)parentExp = &retExp[currExp->parentExpIndex];//bug fixed: changed to currExp->parentExpIndex != 0xFFFFFFFF
                        else parentExp = nullptr;//A|B|C&D&E&F|G|Y|Z
                    }
                    else do_ANDcurr_add_NewORparent(retExp, currExp, parentExp);
                }
                else if (currExp->oper == boolOperator::NOTHING)  //currExp->oper == boolOperator::NOTHING
                    currExp->oper = boolOperator::OR;
                
                break;
            case '~':
                currExp->flipNegate();
                break;
            case '(': {//like normal A-Z, it's a variable with other variables inside
                currExp->setValFound(retExp.size() + 28, 0);
                addNewExp(retExp, currExp, parentExp, currExp->lv + 1, 0u);
                parentExp = &*currExp;
                currExp = &retExp.back();
                currExp->parentExpIndex = parentExp->expIndex - 28u;
                break;
            }
            case ')': {
                if (currExp->oper == boolOperator::NOTHING) {// (((A))), ~((A))
                    parentExp->takeOverCurrInfo(*currExp);

                    if (currExp->valFound.second == 0)
                        retExp[currExp->valFound.first - 28u].parentExpIndex = parentExp->expIndex - 28u;

                    currExp->lv = -999999;
                    //retExp.pop_back(); fix bug: can't use this
                }
                else {
                    addValAny(currExp, newNumBoolFound, varFound);
                    if (currExp->oper == boolOperator::AND && parentExp->oper == boolOperator::OR && currExp->hasNoBracket) {//bug fixed: add hasNoBracket for case (C|D&A)
                        currExp = &(*parentExp);
                        parentExp = &retExp[currExp->parentExpIndex];
                    }
                }
                currExp = &(*parentExp);
                if (currExp->parentExpIndex != 0xFFFFFFFF)parentExp = &retExp[currExp->parentExpIndex];//bug fixed: changed to currExp->parentExpIndex != 0xFFFFFFFF
                else parentExp = nullptr;
                break;
            }
            default:
                currExp->setValFound(exp[i], 1);//cant add new variable until the next oper sign is not |
                break;
            }
        }
        //cout << "\n";
        addValAny(currExp, newNumBoolFound, varFound);
    }
    static void addNewExp(vector<Expression>& retExp, Expression*& currExp, Expression*& parentExp, const int lv, const size_t hasNoBracket) {
        //vector recopy everything to the new address when it reachs its capacity
        //******this function doesn't change currExp/parentExp******
        size_t indexCurr = currExp->expIndex - 28, indexPar;
        if (parentExp)indexPar = parentExp->expIndex - 28u;
        retExp.emplace_back(lv, retExp.size() + 28u, hasNoBracket);
        currExp = &retExp[indexCurr]; 
        if (parentExp)parentExp = &retExp[indexPar];
    }
    static void addValAny(Expression*& currExp, size_t& newNumBoolFound, size_t*& varFound) {
        if(currExp->valFound.second) addCharVar(currExp, currExp->valFound.first, newNumBoolFound, varFound); 
        else currExp->addVal(currExp->valFound.first);
    }
    static void addCharVar(Expression*& currExp, const char valFound, size_t& newNumBoolFound, size_t*& varFound) {
        const int index = valFound - 65;
        currExp->addVal(index);
        newNumBoolFound += !varFound[index]; // == 0
        varFound[index] |= 1u;
    }
    static void do_ORcurr_add_NewANDchild(vector<Expression>& retExp, Expression*& currExp, Expression*& parentExp, size_t& newNumBoolFound, size_t*& varFound) {
        addNewExp(retExp, currExp, parentExp, currExp->lv + 1, 1u);
        parentExp = &*currExp;
        currExp = &retExp.back();

        currExp->parentExpIndex = parentExp->expIndex - 28u;
        currExp->oper = boolOperator::AND;
        currExp->setValFound(parentExp->valFound.first, parentExp->valFound.second);
        currExp->foundNegate = parentExp->foundNegate;
        addValAny(currExp, newNumBoolFound, varFound);

        parentExp->setValFound(currExp->expIndex, 0);
        parentExp->foundNegate = 0;
        addValAny(parentExp, newNumBoolFound, varFound);//ex: A|B|C&D&()&Y|S|G&U&P&()|M = A|B|(exp)|S|(exp)|M 
    }
    static void do_ANDcurr_add_NewORparent(vector<Expression>& retExp, Expression*& currExp, Expression*& parentExp) {
        /*
        A&B|C
        (O&M|A)
        A&(~(~(O&M|~D&M))|~E)
        */
        if (currExp->parentExpIndex != 0xFFFFFFFF) {//fixed bug: A&(~(~(O&M|~D&M))|~E)
            addNewExp(retExp, currExp, parentExp, currExp->lv, 1u);
            shiftLV(retExp, currExp);
        }
        else //fix bug: (~A|B)&(C|D&~F)|F
            addNewExp(retExp, currExp, parentExp, currExp->lv - 1, 1u);//shiftLV maybe expensive

        Expression* newORParent = &retExp.back();
        newORParent->parentExpIndex = currExp->parentExpIndex;//parentExp doesn't change
        newORParent->oper = boolOperator::OR;
        newORParent->addVal(currExp->expIndex);
        if(parentExp != nullptr)parentExp->valFound.first = newORParent->expIndex;//fix bug: (O&M|A), A&B|C

        currExp->parentExpIndex = newORParent->expIndex - 28u;
        currExp = &*newORParent;//old currExp will not has any new variable
    }
    static void shiftLV(vector<Expression>& retExp, Expression* currExp) {
        currExp->lv += 1u;
        FOR (i, currExp->len) {
            size_t expIndex = currExp->vals[i] & 0x7FFFFFFFu;
            if (expIndex > 27) shiftLV(retExp, &retExp[expIndex - 28u]);
        }
    }
};

struct sortExpression{
    inline bool operator() (const Expression& exp1, const Expression& exp2){
        return (exp1.lv > exp2.lv);
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
        const size_t prev_boolIndexLen = prev.boolIndexLen;

        size_t allPossBool, newNumBoolFound = 0, varFound[26] = { 0u };//bitset: 2=old stack has variable, 1=found, 3=2|1, 0=not found          
        FOR(i, prev_boolIndexLen) {
            varFound[prev.boolVarIndex[i]] = 2u;
            boolVarIndex[i] = prev.boolVarIndex[i];
        }

        vector<Expression> exps;
        ExpressionBuilder::stringToExp(exps, cond, newNumBoolFound, varFound);
        std::sort(exps.begin(), exps.end(), sortExpression());
        while (exps.back().lv < -10) exps.pop_back();

        allPossBool = 1u << newNumBoolFound;//works on case: newNumBoolFound = 0

        boolIndexLen = prev_boolIndexLen;
        FOR(i, 26u)
            if (varFound[i] == 1u)// 0|1=1, 2|1=3
                boolVarIndex[boolIndexLen++] = i;        
        
        size_t memVal[75];//0-25=A-Z, 26=0, 27=1, 28-74=Exps
        memVal[26] = 0u; memVal[27] = 1u;

        uint32_t(*boolOperation[3])(uint32_t*, uint32_t, uint32_t*) = {
            { [](uint32_t* expVals, uint32_t expValslen, uint32_t* valMem) { uint32_t ret = VALWNEGATE(valMem,0,expVals); FOR1(i,expValslen) ret &= VALWNEGATE(valMem,i,expVals); return ret; } },
            { [](uint32_t* expVals, uint32_t expValslen, uint32_t* valMem) { uint32_t ret = VALWNEGATE(valMem,0,expVals); FOR1(i,expValslen) ret |= VALWNEGATE(valMem,i,expVals); return ret; } },
            { [](uint32_t* expVals, uint32_t expValslen, uint32_t* valMem) { return VALWNEGATE(valMem,0,expVals); } }
        };

        const size_t lastExpsIndex = exps.size() - 1;
        for (uint32_t prevAnsMem : prev.allAns[prev.condState]) {

            FOR(i, prev_boolIndexLen) {//if prev_boolIndexLen == 0; FOR(j, prev_boolIndexLen, boolIndexLen) will do the job
                const size_t bit = prevAnsMem >> i & 1u;
                memVal[boolVarIndex[i]] = bit;
            }

            FOR(i, allPossBool) {
                uint32_t result, boolmem = prevAnsMem | (i << prev_boolIndexLen);//assuming that shifted int is follow by 0s

                FORS(j, prev_boolIndexLen, boolIndexLen) {
                    const size_t bit = boolmem >> j & 1u;
                    memVal[boolVarIndex[j]] = bit;
                }

                FOR(j, exps.size())
                    memVal[exps[j].expIndex] = boolOperation[exps[j].oper](exps[j].vals, exps[j].len, memVal);

                result = memVal[exps[lastExpsIndex].expIndex];
                allAns[result].push_back(boolmem);

                FOR(j, boolIndexLen) {
                    const uint32_t index = boolVarIndex[j], currBit = memVal[index];
                    if (finalAns[result][index] == -3)finalAns[result][index] = currBit;
                    else if (finalAns[result][index] != currBit)finalAns[result][index] = -1;
                }
            }
        }

        if (allAns[0].empty())finalAns[0][0] = -2;
        else if (allAns[1].empty())finalAns[1][0] = -2;
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

int main() {
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