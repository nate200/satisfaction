#include<iostream>
#include<stack>
#include<vector>
#include<unordered_set>
#include<algorithm>

#include <time.h>
#define FOR(i, n) for (size_t i = 0u; i < n; i++)
#define FORS(i, s, n) for (size_t i = s; i < n; i++)
#define FOR1(i, n) for (size_t i = 1u; i < n; i++)
#define FOR1p(s, e) for (s++; s < e; s++)

using namespace std;

enum boolOperator { AND = 0, OR = 1, NOTHING = 2 }; //replace with integer, can't convert enum to int ;(
struct Expression {//1 boolean operation per 1 expression
    boolOperator oper = boolOperator::NOTHING;

    size_t expIndex, len = 0, *vals = NULL;//0-25=A-Z, 26=true, 27-70=an index of an Expression, 32th-bit for negation
    int lv;//highest lv will be calculated first, children have higher lv than their parent
    //vector<size_t> *valsVector = nullptr;
    Expression(boolOperator oper, int lv, size_t expInfo_expIndex, unordered_set<size_t>& expInfo_vals, size_t* indexMapper)
        : oper(oper), lv(lv){
        len = expInfo_vals.size();
        expIndex = indexMapper[expInfo_expIndex];

        vals = new size_t[len];
        size_t* it_val = vals;

        //valsVector = new vector<size_t>;
        //valsVector->reserve(len);

        for (const size_t val : expInfo_vals) {
            *it_val = indexMapper[val & 0x7FFFFFFF] | val & 0x80000000;
            //valsVector->push_back(*it_val);
            it_val++;
        }
    }
    ~Expression() { if(vals) delete[] vals; /*delete valsVector;*/ }
};
struct ExpressionBuilder {
    ExpressionBuilder() { throw ""; }

    struct ExpressionInfo {//1 boolean operation per 1 expression
        boolOperator oper = boolOperator::NOTHING;

        size_t expIndex;
        unordered_set<size_t> vals;//not sorted: 0-25=A-Z, 26=true, 27-70=an index of an Expression, 32th-bit for negation
        int lv = -9999999;//highest lv will be calculated first, children have higher lv than their parent

        uint32_t valFound, nthChanged = 1;

        ExpressionInfo* baseLine = nullptr, * holdingChild = nullptr;//vector won't reallocate because of reserve(96);
        size_t foundNegate = 0;

        vector<size_t> valsVec;

        ExpressionInfo(boolOperator oper, size_t expCounter, ExpressionInfo* baseLine = nullptr) : oper(oper), expIndex(expCounter), baseLine(&*baseLine) {}

        static constexpr size_t negate32thBit[2] = { 0u , 0x80000000 };
        
        void flip_foundNegate() { foundNegate = !foundNegate; }
        void addValFound(vector<ExpressionInfo> & expInfos) {
            if (valFound > 26u) {
                ExpressionInfo * chExp = &expInfos[valFound - 26u];
                if (chExp->oper == boolOperator::NOTHING) {
                    vals.insert(*chExp->vals.begin() ^ negate32thBit[foundNegate]);
                    if (&expInfos.back() == chExp)
                        expInfos.pop_back();
                }
                else vals.insert(valFound | negate32thBit[foundNegate]);
            }
            else vals.insert(valFound | negate32thBit[foundNegate]);
            foundNegate = 0;
        }
        void addAllValsFromExpValFound(ExpressionInfo& exp, uint32_t expNegate) {
            const size_t fn = negate32thBit[foundNegate ^ expNegate];
            for (const size_t val : exp.vals)
                vals.insert(val ^ fn);
        }
        void addValFound_FromOR(vector<ExpressionInfo>& expInfos, ExpressionInfo *exp) {
            valFound = exp->valFound;
            foundNegate = exp->foundNegate;
            addValFound(expInfos);// A|B&C, A|~()&C
        }
        void tryTakingOverChild(vector<ExpressionInfo> &expInfos) {
            const size_t val = *vals.begin(), index = val & 0x7FFFFFFF;
            if (index < 27) return;

            ExpressionInfo* valExp = &expInfos[index - 26u];

            oper = boolOperator(valExp->oper ^ val >> 31);
            vals.clear();

            const size_t fn = negate32thBit[val >> 31];
            for (const size_t ch_val : valExp->vals)
                vals.insert(ch_val ^ fn);

            valExp->vals.clear();
            valExp->oper = boolOperator::NOTHING;
        }
        void addSetToVector() { 
            valsVec.reserve(vals.size());
            std::copy(vals.begin(), vals.end(), std::back_inserter(valsVec));
        }
        inline bool operator<(const ExpressionInfo& exp) const
        {
            return lv > exp.lv;
        }
        ~ExpressionInfo() { }
    };

    static void stringToExp(vector<Expression>& retExp, const char* exp) {

        vector<ExpressionInfo> expInfos;
        expInfos.reserve(70);//prevent reallocation which will mess up all the address

        ExpressionInfo* baseLine, * currExp;
        expInfos.emplace_back(boolOperator::NOTHING, 26u, nullptr);//baseLine
        baseLine = &expInfos.back();
        expInfos.emplace_back(boolOperator::NOTHING, 27u, baseLine);
        currExp = &expInfos.back();
        baseLine->holdingChild = currExp;

        for (size_t i = 0u; exp[i] != '\0'; i++) {
            //cout << exp[i];
            switch (exp[i]) {
            case '&':
                switch (currExp->oper) {
                case boolOperator::AND:
                    currExp->addValFound(expInfos);
                    break;
                case boolOperator::OR:
                    add_ANDexp_to_ORcurr(expInfos, currExp);
                    break;
                case boolOperator::NOTHING:
                    currExp->oper = boolOperator::AND;
                    currExp->addValFound(expInfos);
                    break;
                }
                break;
            case '|':
                switch (currExp->oper) {
                case boolOperator::AND:
                    currExp->addValFound(expInfos);
                    if (baseLine->holdingChild->oper == boolOperator::OR) {
                        currExp = baseLine->holdingChild;//go back to OR
                        currExp->addValFound(expInfos);// E|A&B|C => E|()|C
                    }
                    else add_ORexp_with_ANDcurr(expInfos, baseLine, currExp);
                    break;
                case boolOperator::OR:
                    currExp->addValFound(expInfos);
                    break;
                case boolOperator::NOTHING:
                    currExp->oper = boolOperator::OR;
                    currExp->addValFound(expInfos);
                    break;
                }
                break;
            case '~':
                currExp->flip_foundNegate();
                break;
            case '(': //like normal A-Z, it's a variable with other variables inside
                add_baseLine_to_currExp(expInfos, baseLine, currExp);
                break;
            case ')': {//can't merge child and baseline with the same oper in here, case: A|(B|C)&D
                currExp->addValFound(expInfos);
                if (baseLine->holdingChild != currExp) //D&(A|B&C)
                    baseLine->holdingChild->addValFound(expInfos);

                currExp = currExp->baseLine;
                baseLine = currExp->baseLine;
                break;
            }
            default:
                currExp->valFound = exp[i] - 65u;//cant add new variable until the next oper sign is known
                break;
            }
        }
        //cout << "\n";
        currExp->addValFound(expInfos);
        if (baseLine->holdingChild != currExp) //fix bug: A&B|C&(Z&X)
            baseLine->holdingChild->addValFound(expInfos);

        currExp = baseLine->holdingChild;

        if (currExp->oper == boolOperator::NOTHING) //fix bug: ~(A&B)
            currExp->tryTakingOverChild(expInfos);

        uint32_t isAnyAdded = walkTreeExp(expInfos, currExp, 0, currExp->expIndex);

        size_t indexMapper[98];
        FOR(i, 27u) indexMapper[i] = i;

        if (isAnyAdded) {
            simpEqs(expInfos, indexMapper);

            size_t index = 27u;
            for (const ExpressionInfo& exp : expInfos)
                indexMapper[exp.expIndex] = index++;

            retExp.reserve(expInfos.size());
            for (ExpressionInfo& expp : expInfos)
                retExp.emplace_back(expp.oper, expp.lv, expp.expIndex, expp.vals, indexMapper);
        }
        else {
            currExp = baseLine->holdingChild;
            indexMapper[27u] = 27u;
            retExp.emplace_back(currExp->oper, 0, 27u, currExp->vals, indexMapper);
        }
    }
    static uint32_t walkTreeExp(vector<ExpressionInfo>& expInfos, ExpressionInfo * currExp, const int lv, size_t pindex) {
        uint32_t isAdded = 0;
        if (currExp->oper != boolOperator::NOTHING) {
            currExp->lv = lv;
            isAdded = 1;
        }

        const int nextLv = lv + 1;
        pindex = currExp->expIndex;
        for (const size_t val : currExp->vals) {
            size_t index = val & 0x7FFFFFFF;
            if (index > 26) 
                isAdded |= walkTreeExp(expInfos, &expInfos[index - 26u], nextLv, pindex);
        }
        return isAdded;
    }

    static void add_ORexp_with_ANDcurr(vector<ExpressionInfo>& expInfos, ExpressionInfo*& baseLine, ExpressionInfo*& currExp) {
        expInfos.emplace_back(boolOperator::OR, expInfos.size() + 26u, baseLine);
        ExpressionInfo* newORexp = &expInfos.back();
        newORexp->valFound = currExp->expIndex;
        newORexp->addValFound(expInfos);// A&B|C

        baseLine->valFound = newORexp->expIndex;//fix bug: B&((((A)&C|D))), forgot to change valFound
        baseLine->holdingChild = newORexp;
        currExp = newORexp;
    }
    static void add_ANDexp_to_ORcurr(vector<ExpressionInfo>& expInfos, ExpressionInfo*& currExp) {
        expInfos.emplace_back(boolOperator::AND, expInfos.size() + 26u, currExp->baseLine);
        ExpressionInfo* newANDexp = &expInfos.back();
        newANDexp->addValFound_FromOR(expInfos, currExp);

        currExp->valFound = newANDexp->expIndex;
        currExp->foundNegate = 0;

        currExp = newANDexp;
    }
    static void add_baseLine_to_currExp(vector<ExpressionInfo>& expInfos, ExpressionInfo*& baseLine, ExpressionInfo*& currExp) {
        expInfos.emplace_back(boolOperator::NOTHING, expInfos.size() + 26u, currExp);
        ExpressionInfo* newExp = &expInfos.back();

        currExp->holdingChild = newExp;
        currExp->valFound = newExp->expIndex;//~()&A, ()|A, ()

        baseLine = currExp;
        currExp = newExp;
    }

    static void simpEqs(vector<ExpressionInfo>& expInfos, size_t * indexMapper) {
        sort(expInfos.begin(), expInfos.end());
        while (expInfos.back().lv < 0) expInfos.pop_back();

        size_t anyEqsChanged = 0;
        for (ExpressionInfo& exp : expInfos) { 
            exp.addSetToVector();
            indexMapper[exp.expIndex] = anyEqsChanged++;
        }
        anyEqsChanged = 0;

        for(ExpressionInfo & currExp : expInfos) {

            unordered_set<size_t>* valsSet = &currExp.vals;
            vector<size_t>* valsVec = &currExp.valsVec;

            FOR (i, valsVec->size()) {
                const size_t val = valsVec->at(i);
                size_t rawVal = val & 0x7FFFFFFF;

                if (rawVal > 26u) {
                    size_t val_negate = val & 0x80000000;
                    ExpressionInfo* chExp = &expInfos[indexMapper[rawVal]];

                    /*if (chExp->oper == boolOperator::NOTHING) {
                        size_t chVal = *chExp->vals.begin(), raw_chVal = chVal & 0x7FFFFFFF, reduced = 0;

                        if (raw_chVal == 26u && currExp.oper != (val_negate >> 31 ^ chVal >> 31)) {
                            walkClearVals(&currExp, expInfos, indexMapper);
                            valsSet->insert(26u ^ !currExp.oper << 31);
                            currExp.oper = boolOperator::NOTHING;
                            reduced = 1;
                        }
                        else if (raw_chVal != 26u) {
                            chVal ^= val_negate;
                            if (valsSet->find(chVal) != valsSet->end())continue;
                            valsVec->push_back(chVal);
                            valsSet->insert(chVal);
                        }

                        chExp->oper = boolOperator::NOTHING;
                        chExp->vals.clear();

                        valsSet->erase(val);

                        anyEqsChanged = 1;

                        if (reduced)break;
                    }
                    else */if ((currExp.oper == chExp->oper) ^ val_negate >> 31) {// A&~(A|B)  ,  A|~(A&B)  , A&(A&B)  , A|(A|B)

                        valsSet->erase(val);

                        for (size_t chVal : chExp->vals) {
                            chVal ^= val_negate;
                            if (valsSet->find(chVal) != valsSet->end())continue;
                            valsVec->push_back(chVal);
                            valsSet->insert(chVal);
                        }
                        
                        anyEqsChanged = 1;

                        chExp->vals.clear();
                        chExp->oper = boolOperator::NOTHING;
                    }
                }

                else if (valsSet->find(val ^ 0x80000000) != valsSet->end()) {
                    walkClearVals(&currExp, expInfos, indexMapper);
                    valsSet->insert(26u ^ !currExp.oper << 31);
                    currExp.oper = boolOperator::NOTHING;
                    anyEqsChanged = 1;
                    valsVec->clear();
                    break;
                }

            }
            if (valsSet->size() == 1)currExp.oper = boolOperator::NOTHING;
            valsVec->clear();
        }

        if (anyEqsChanged) 
            expInfos.erase(
                remove_if(expInfos.begin(), expInfos.end(), [](const  ExpressionInfo& exp) { return exp.vals.empty(); }), 
                expInfos.end()
            );
    }
    static void walkClearVals(ExpressionInfo* currExp, vector<ExpressionInfo>& expInfos, size_t* indexMapper) {
        for (size_t val : currExp->vals) {
            val &= 0x7FFFFFFF;
            if (val > 26u) {
                ExpressionInfo* tempExp = &expInfos[indexMapper[val]];
                tempExp->oper = boolOperator::NOTHING;
                walkClearVals(tempExp, expInfos, indexMapper);
            }
        }
        currExp->vals.clear();
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
        if (prev.finalAns[prev.condState][0] == -2) {//unreachable, fix bug change condState to prev.condState
            finalAns[0][0] = finalAns[1][0] = -2;
            return;
        }
        FOR(i, 26u) finalAns[0][i] = finalAns[1][i] = -3;
        getStackAns(cond, prev);
    }

    void getStackAns(const char* cond, const CondStack& prev) {
        const size_t prev_boolIndexLen = prev.boolIndexLen;

        size_t allPossBool = 0;
        vector<Expression> exps;
        {
            size_t varFound[26] = { 0u };//bitset: 2=old stack has variable, 1=found, 3=2|1, 0=not found          
            FOR(i, prev_boolIndexLen) {
                varFound[prev.boolVarIndex[i]] = 2u;
                boolVarIndex[i] =  prev.boolVarIndex[i];
            }

            ExpressionBuilder::stringToExp(exps, cond);

            for (const Expression& exp : exps) {
                size_t* valsEnd = exp.vals + exp.len;
                for (size_t* val = exp.vals; val < valsEnd; val++) {
                    const size_t index = *val & 0x7FFFFFFF;
                    if (index > 25) continue;
                    allPossBool += !varFound[index]; // == 0
                    varFound[index] |= 1u;
                }
            }
            
            allPossBool = 1u << allPossBool;//works on case: newNumBoolFound = 0

            boolIndexLen = prev_boolIndexLen;
            FOR(i, 26u) 
                if (varFound[i] == 1u) // 0|1=1, 2|1=3
                    boolVarIndex[boolIndexLen++] = i;
        }

        size_t findValAns[2][26], findValAnsLen[2];
        findValAnsLen[0] = findValAnsLen[1] = boolIndexLen;
        FOR(i, boolIndexLen) findValAns[0][i] = findValAns[1][i] = boolVarIndex[i];

        uint32_t memVal[75];//array index: [0-25=A-Z], [26=true], [27-74=Exps]
        memVal[26] = 1u;

        //added to prevent vector reallocation
        uint32_t ansLen = prev.allAns[prev.condState].size() * allPossBool;
        uint32_t* allAnsTemp = new uint32_t[ansLen], *allAnsTempResult = new uint32_t[ansLen];
        uint32_t ansLenEach[2] = { 0,0 };
        ansLen = 0;

        uint32_t* lastExpResult = &memVal[27u + exps.size() - 1];
        for (uint32_t prevAnsMem : prev.allAns[prev.condState]) {

            FOR(i, prev_boolIndexLen) 
                memVal[boolVarIndex[i]] = prevAnsMem >> i & 1u;

            FOR(i, allPossBool) {
                uint32_t boolmem = prevAnsMem | i << prev_boolIndexLen;
                FORS(j, prev_boolIndexLen, boolIndexLen)
                    memVal[boolVarIndex[j]] = boolmem >> j & 1u;

                for (const Expression& exp : exps) {//dereferencing an array of exps is slow, removed by using foreach
                    //memVal[exp.expIndex] = boolOperation[exp.oper](exp.vals, exp.vals + exp.len, memVal);
                    size_t * expVals = exp.vals, *expVale = exp.vals + exp.len;
                    uint32_t ret = memVal[expVals[0] & 0x7FFFFFFF] ^ (expVals[0] >> 31);
                    switch (exp.oper) {
                    case boolOperator::AND: 
                        FOR1p(expVals, expVale) 
                            ret &= memVal[*expVals & 0x7FFFFFFF] ^ (*expVals >> 31);
                        break;
                    case boolOperator::OR: 
                        FOR1p(expVals, expVale) 
                            ret |= memVal[*expVals & 0x7FFFFFFF] ^ (*expVals >> 31);
                        break;
                    }
                    memVal[exp.expIndex] = ret;
                }

                const uint32_t result = *lastExpResult;

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
        FOR(i, ansLen) 
            allAns[allAnsTempResult[i]].push_back(allAnsTemp[i]);

        if (ansLenEach[0] == 0)finalAns[0][0] = -2;
        else if (ansLenEach[1] == 0)finalAns[1][0] = -2;

        delete[] allAnsTempResult; delete[] allAnsTemp;
    }

    void switchToElse() {
        condState = 0;
        allAns[1].clear();
        allAns[1].reserve(0);
    }

    void checkpoint() {  
        cout << '>';
        if (finalAns[condState][0] == -2)cout << "unreachable";
        else {
            FOR(i, 26u)//fix bug : change from boolIndexLen to 26u. wtf is wrong with me
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
    /*while (cin >> cond) {
        ifs.emplace(cond, ifs.top());
        ifs.pop();
    }*/
    while (cin >> inputState) {
        switch (inputState[0]) {
        case Statement::IF : {//if
            cin >> cond >> then;
            //const clock_t start = clock();
            ifs.emplace(cond, ifs.top());
            //cout << clock() - start << "\n";
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