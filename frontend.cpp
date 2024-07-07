// lexer breaks the lang into tokens

#include <llvm/IR/Constants.h>
#include <llvm/IR/PassManager.h>
#include "./include/KaleidoscopeJIT.h"
#include <llvm/Support/TargetSelect.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Passes/StandardInstrumentations.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/Reassociate.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Module.h>
#include <llvm/ADT/APFloat.h>
#include <llvm/IR/Type.h>
#include <llvm/Support/raw_ostream.h>
#include <memory>
#include <map>
#include <llvm/IR/Value.h>
#include <llvm/IR/IRBuilder.h>
#include <utility>
#include <vector>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <string>

enum Token {
  tok_eof = -1,
  tok_def = -2,
  tok_extern = -3,
  tok_identifier = -4,
  tok_number = -5,
};

static std::string IdentifierStr;
static double NumVal;

static int gettok(){
    static int LastChar = ' ';
    while (isspace(LastChar)) {
        LastChar = getchar();
    }
    if (isalpha(LastChar)) {
        IdentifierStr = LastChar;
        while (isalnum(LastChar = getchar())) {
            IdentifierStr+=LastChar;
        }
        if (IdentifierStr == "def") {
            return tok_def;
        }
        if (IdentifierStr == "extern") {
            return tok_extern;
        }
        return tok_identifier;
    }
    if (isdigit(LastChar) || LastChar == '.') {
        std::string NumStr;
        do {
            NumStr += LastChar;
            LastChar = getchar();
        }while (isdigit(LastChar) || LastChar == '.');

        NumVal = strtod(NumStr.c_str(), 0);
        return tok_number;
    }
    if (LastChar == '#') {
        do {
            LastChar = getchar();
        }while (LastChar!=EOF && LastChar != '\n' && LastChar!='\r');
        if (LastChar!=EOF) {
            return gettok();
        }
    }
    if (LastChar == EOF) {
        return tok_eof;
    }
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
}

class ExprAST {
    public:
        virtual ~ExprAST() = default;
        virtual llvm::Value *codegen() = 0;
};
class NumberExprAST: public ExprAST{
    double Val;
    public:
    NumberExprAST(double Val): Val(Val){}
    llvm::Value *codegen() override;
};

class VariableExprAST : public ExprAST{
    std::string Name;
    public:
    VariableExprAST(const std::string &Name): Name(Name) {};
    llvm::Value *codegen() override;
};
class BinaryOpAST : public ExprAST{
    char Op;
    std::unique_ptr<ExprAST> LHS, RHS;
    public:
    BinaryOpAST(char Op, std::unique_ptr<ExprAST> LHS,std::unique_ptr<ExprAST> RHS): Op(Op),LHS(std::move(LHS)),RHS(std::move(RHS)){};
    llvm::Value *codegen() override;
};

class CallAST: public ExprAST{
    std::string Callee;
    std::vector<std::unique_ptr<ExprAST>> Args;
    public:
    CallAST(const std::string &Callee,std::vector<std::unique_ptr<ExprAST>> Args) : Callee(Callee), Args(std::move(Args)) {}
    llvm::Value *codegen() override;
};

class ProtoAST {
    std::string Name;
    std::vector<std::string> Args;
    public:
    llvm::Function *codegen();
    ProtoAST(const std::string &Name, std::vector<std::string> Args): Name(Name), Args(std::move(Args)) {};
    const std::string &getName() const {return Name;}
};

class FuncAST{
    std::unique_ptr<ProtoAST> Proto;
    std::unique_ptr<ExprAST> Body;
    public:
    llvm::Function *codegen();
    FuncAST(std::unique_ptr<ProtoAST> Proto,
            std::unique_ptr<ExprAST> Body): Proto(std::move(Proto)),Body(std::move(Body)){};
};

// building the parser

// logic to fetch the subsequent tokens from the lexer.
static int Curtok;
static int getNextTok(){
    return Curtok = gettok();
}
static std::unique_ptr<ExprAST> ParseExpression();
// helper functions to handle errors.
std::unique_ptr<ExprAST> LogErr(const char *str){
    fprintf(stderr, "Error: %s\n",str);
    return nullptr;
}
std::unique_ptr<ProtoAST> LogErrP(const char *str){
    LogErr(str);
    return nullptr;
}

// parser logic starts 
// Numeric Literals. Called when tok_number is encountered.
static std::unique_ptr<ExprAST> ParseNumerExpr(){
    auto Result = std::make_unique<NumberExprAST>(NumVal);
    getNextTok();
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseParenExpr() {
    getNextTok();
    auto V = ParseExpression();
    if (!V) {
        return nullptr;
    }
    if (Curtok != ')') {
        return LogErr("Expected ')'");
    }
    getNextTok();
    return V;
}

static std::unique_ptr<ExprAST> ParseIdenExpr(){
    std::string Id = IdentifierStr;

    getNextTok();
    if (Curtok!='(') {
        return std::make_unique<VariableExprAST>(Id);
    }
    getNextTok();
    std::vector<std::unique_ptr<ExprAST>> Args;
    if (Curtok!=')') {
        while (true) {
            if (auto Arg = ParseExpression()) {
                Args.push_back(std::move(Arg));
            }
            if (Curtok == ')') {
                break;
            }
            if (Curtok!=',') {
                return LogErr("Expected ')' or ',' in arguments.");
            }
            getNextTok();
        }
    }

    getNextTok();
    return std::make_unique<CallAST>(Id,std::move(Args));
}

static std::unique_ptr<ExprAST> ParsePrimary(){
    switch (Curtok) {
        default : 
            return LogErr("Unknown token while parsing expression.");
        case tok_identifier:
            return ParseIdenExpr();
        case tok_number:
            return ParseNumerExpr();
        case '(':
            return ParseParenExpr();
    }
}

// Binary Expression Parsing

static std::map<char, int> BinopPrecedence;

static int GetTokPrecedence() {
    if (!isascii(Curtok))
        return -1;

    int TokPrec = BinopPrecedence[Curtok];
    if (TokPrec <= 0) return -1;
    return TokPrec;
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
        std::unique_ptr<ExprAST> LHS) {
    while (true) {
        int TokPrec = GetTokPrecedence();

        if (TokPrec < ExprPrec)
            return LHS;

        int BinOp = Curtok;
        getNextTok();

        auto RHS = ParsePrimary();
        if (!RHS)
            return nullptr;

        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec) {
            RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
            if (!RHS)
                return nullptr;
        }

        LHS =
            std::make_unique<BinaryOpAST>(BinOp, std::move(LHS), std::move(RHS));
    }
}
static std::unique_ptr<ExprAST> ParseExpression() {
    auto LHS = ParsePrimary();
    if (!LHS)
        return nullptr;

    return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ProtoAST> ParseProto() {
    if (Curtok!= tok_identifier) {
        return LogErrP("Expected identifier in function prototype!");
    } 
    std::string funcName = IdentifierStr;
    getNextTok();
    if (Curtok!='(') {
        return LogErrP("Expected '(' in function prototype!");
    }
    std::vector<std::string> Args;
    while (getNextTok()==tok_identifier) {
        Args.push_back(IdentifierStr);
    }
    if (Curtok!=')') {
        return LogErrP("Expected ')' in function prototype");
    }
    getNextTok();
    return std::make_unique<ProtoAST>(IdentifierStr,std::move(Args));
}

static std::unique_ptr<FuncAST> ParseDef(){
    getNextTok();
    auto proto = ParseProto();
    if (!proto) {
        return nullptr;
    }
    if (auto E = ParseExpression()) {
        return std::make_unique<FuncAST>(std::move(proto),std::move(E));
    }
    return nullptr;
}

static std::unique_ptr<ProtoAST> ParseExtern(){
    getNextTok();
    return ParseProto();
}

static std::unique_ptr<FuncAST> ParseTopLevelExpr() {
    if (auto E = ParseExpression()) {
        auto Proto = std::make_unique<ProtoAST>("", std::vector<std::string>());
        return std::make_unique<FuncAST>(std::move(Proto), std::move(E));
    }
    return nullptr;
}

static std::unique_ptr<llvm::LLVMContext> TheContext; // For LLVMContext. Allocates LLVM structures.
static std::unique_ptr<llvm::IRBuilder<>> Builder; // helper class to create and insert instructions into blocks.
                                                   // This implements Constant Folding so our AST doesn't need to be uglified having constant checks.
static std::unique_ptr<llvm::Module> TheModule; // a single file's worth of code that gets compiled. Functions, globals etc. Basic unit of LLVM IR that we get when we pass the --emit-llvm flag to clang.
static std::map<std::string, llvm::Value *> NamedValues; // a symbol table of values.

static std::unique_ptr<llvm::FunctionPassManager> TheFPM;
static std::unique_ptr<llvm::LoopAnalysisManager> TheLAM;
static std::unique_ptr<llvm::FunctionAnalysisManager> TheFAM;
static std::unique_ptr<llvm::CGSCCAnalysisManager> TheCGAM;
static std::unique_ptr<llvm::ModuleAnalysisManager> TheMAM;
static std::unique_ptr<llvm::PassInstrumentationCallbacks> ThePIC;
static std::unique_ptr<llvm::StandardInstrumentations> TheSI;
static std::map<std::string, std::unique_ptr<ProtoAST>> FunctionProtos;
static std::unique_ptr<llvm::orc::KaleidoscopeJIT> TheJIT;
static llvm::ExitOnError ExitOnErr;
/*static std::unique_ptr<KaleidoscopeJIT> TheJIT;*/

static void InitializeModule() {
    // Open a new context and module.
    TheContext = std::make_unique<llvm::LLVMContext>();
    TheModule = std::make_unique<llvm::Module>("KaleidoscopeJIT", *TheContext);
    TheModule->setDataLayout(TheJIT->getDataLayout());

    // Create a new builder for the module.
    Builder = std::make_unique<llvm::IRBuilder<>>(*TheContext);

    // Create new pass and analysis managers.
    TheFPM = std::make_unique<llvm::FunctionPassManager>();
    TheLAM = std::make_unique<llvm::LoopAnalysisManager>();
    TheFAM = std::make_unique<llvm::FunctionAnalysisManager>();
    TheCGAM = std::make_unique<llvm::CGSCCAnalysisManager>();
    TheMAM = std::make_unique<llvm::ModuleAnalysisManager>();
    ThePIC = std::make_unique<llvm::PassInstrumentationCallbacks>();
    TheSI = std::make_unique<llvm::StandardInstrumentations>(*TheContext,
            /*DebugLogging*/ true);
    TheSI->registerCallbacks(*ThePIC, TheMAM.get());

    // Add transform passes.
    // Do simple "peephole" optimizations and bit-twiddling optzns.
    TheFPM->addPass(llvm::InstCombinePass());
    // Reassociate expressions.
    TheFPM->addPass(llvm::ReassociatePass());
    // Eliminate Common SubExpressions.
    TheFPM->addPass(llvm::GVNPass());
    // Simplify the control flow graph (deleting unreachable blocks, etc).
    TheFPM->addPass(llvm::SimplifyCFGPass());

    // Register analysis passes used in these transform passes.
    llvm::PassBuilder PB;
    PB.registerModuleAnalyses(*TheMAM);
    PB.registerFunctionAnalyses(*TheFAM);
    PB.crossRegisterProxies(*TheLAM, *TheFAM, *TheCGAM, *TheMAM);
}

static void HandleDefinition() {
  if (auto FnAST = ParseDef()) {
    if (auto *FnIR = FnAST->codegen()) {
      fprintf(stderr, "Read function definition:");
      FnIR->print(llvm::errs());
      fprintf(stderr, "\n");
      ExitOnErr(TheJIT->addModule(
          llvm::orc::ThreadSafeModule(std::move(TheModule), std::move(TheContext))));
      InitializeModule();
    }
  } else {
    // Skip token for error recovery.
     getNextTok();
  }
}

static void HandleExtern() {
  if (auto ProtoAST = ParseExtern()) {
    if (auto *FnIR = ProtoAST->codegen()) {
      fprintf(stderr, "Read extern: ");
      FnIR->print(llvm::errs());
      fprintf(stderr, "\n");
      FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
    }
  } else {
    // Skip token for error recovery.
    getNextTok();
  }
}
static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (auto FnAST = ParseTopLevelExpr()) {
    if (FnAST->codegen()) {
      // Create a ResourceTracker to track JIT'd memory allocated to our
      // anonymous expression -- that way we can free it after executing.
      auto RT = TheJIT->getMainJITDylib().createResourceTracker();

      auto TSM = llvm::orc::ThreadSafeModule(std::move(TheModule), std::move(TheContext));
      ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
      InitializeModule();

      // Search the JIT for the __anon_expr symbol.
      auto ExprSymbol = ExitOnErr(TheJIT->lookup("__anon_expr"));

      // Get the symbol's address and cast it to the right type (takes no
      // arguments, returns a double) so we can call it as a native function.
      double (*FP)() = ExprSymbol.getAddress().toPtr<double (*)()>();
      fprintf(stderr, "Evaluated to %f\n", FP());

      // Delete the anonymous expression module from the JIT.
      ExitOnErr(RT->remove());
    }
  } else {
    // Skip token for error recovery.
    getNextTok();
  }
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
    while (true) {
        fprintf(stderr, "ready> ");
        switch (Curtok) {
            case tok_eof:
                return;
            case ';': // ignore top-level semicolons.
                getNextTok();
                break;
            case tok_def:
                HandleDefinition();
                break;
            case tok_extern:
                HandleExtern();
                break;
            default:
                HandleTopLevelExpression();
                break;
        }
    }
}


llvm::Value *LogErrorV(const char *Str) {
    LogErr(Str);
    return nullptr;
}

llvm::Function *getFunction(std::string Name) {
  // First, see if the function has already been added to the current module.
  if (auto *F = TheModule->getFunction(Name))
    return F;

  // If not, check whether we can codegen the declaration from some existing
  // prototype.
  auto FI = FunctionProtos.find(Name);
  if (FI != FunctionProtos.end())
    return FI->second->codegen();

  // If no existing prototype exists, return null.
  return nullptr;
}

llvm::Value *NumberExprAST::codegen() {
    return llvm::ConstantFP::get(*TheContext, llvm::APFloat(Val));
}

llvm::Value *VariableExprAST::codegen() {
    llvm::Value *V = NamedValues[Name];
    if (!V) {
        LogErrorV("Unknown Variable Name");
    }
    return V;
}

llvm::Value *BinaryOpAST::codegen() {
    llvm::Value *L = LHS->codegen();
    llvm::Value *R = RHS->codegen();
    if (!L || !R) {
        return nullptr;
    }
    switch (Op) {
        case '+':
            return Builder->CreateFAdd(L, R, "addtmp");
        case '-':
            return Builder->CreateFSub(L, R, "subtmp");
        case '*':
            return Builder->CreateFMul(L, R, "multmp");
        case '<':
            L = Builder->CreateFCmpULT(L, R, "cmptmp");
            return Builder->CreateUIToFP(L, llvm::Type::getDoubleTy(*TheContext),
                    "booltmp");
        default:
            return LogErrorV("invalid binary operator");
    }
}

llvm::Value *CallAST::codegen() {
    llvm::Function *CalleeF = getFunction(Callee);
    if (!CalleeF) {
        return LogErrorV("Unknown Function referenced!");
    }
    if (CalleeF->arg_size()!=Args.size()) {
        LogErrorV("Incorrect number of arguments passed!");
    }
    std::vector<llvm::Value *> ArgsV;
    for (int i = 0 , e = Args.size(); i!=e;++i) {
        ArgsV.push_back(Args[i]->codegen());
        if (!ArgsV.back()) {
            return nullptr;
        }
    }
    return Builder->CreateCall(CalleeF,ArgsV,"calltmp");
}

llvm::Function *ProtoAST::codegen() {
    std::vector<llvm::Type*> Doubles(Args.size(),llvm::Type::getDoubleTy(*TheContext));
    llvm::FunctionType *FT = llvm::FunctionType::get(llvm::Type::getDoubleTy(*TheContext),Doubles,false);
    llvm::Function *F = llvm::Function::Create(FT, llvm::Function::ExternalLinkage,Name,TheModule.get());
    unsigned Idx = 0;
    for (auto &Arg : F->args()) {
        Arg.setName(Args[Idx++]);
    }
    return F;
}

llvm::Function *FuncAST::codegen() {
    llvm::Function *TheFunction = getFunction(Proto->getName());
    if (!TheFunction) {
        TheFunction = Proto->codegen();
    }
    if (!TheFunction) {
        return nullptr;
    }
    if (!TheFunction->empty()) {
        return (llvm::Function*)LogErrorV("Function cannot be redefined.");
    }
    // Create a new basic block to start insertion into.
    llvm::BasicBlock *BB = llvm::BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);

    // Record the function arguments in the NamedValues map.
    NamedValues.clear();
    for (auto &Arg : TheFunction->args())
        NamedValues[std::string(Arg.getName())] = &Arg;

    if (llvm::Value *RetVal = Body->codegen()) {
        Builder->CreateRet(RetVal);

        llvm::verifyFunction(*TheFunction);
        TheFPM->run(*TheFunction, *TheFAM);

        return TheFunction;
    }

    TheFunction->eraseFromParent();
    return nullptr;
}

int main() {
  llvm::InitializeNativeTarget();
  llvm::InitializeNativeTargetAsmPrinter();
  llvm::InitializeNativeTargetAsmParser();

  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40; // highest.

  // Prime the first token.
  fprintf(stderr, "ready> ");
  getNextTok();

  TheJIT = ExitOnErr(llvm::orc::KaleidoscopeJIT::Create());

  InitializeModule();

  // Run the main "interpreter loop" now.
  MainLoop();

  return 0;
}

