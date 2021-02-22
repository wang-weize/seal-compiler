#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

//useful table
//a table placed fuction calls
typedef std::map<Symbol, Decl> CallTable;
CallTable callTbl;
//a table placed global Vars
typedef std::map<Symbol, Symbol> GlobalVariablesTable;
GlobalVariablesTable globalvarsTbl;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print       = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    for(int i = decls->first(); decls->more(i); i = decls->next(i) )
    {
        if(decls->nth(i)->isCallDecl())
        {
            Symbol name = decls->nth(i)->getName();
            Symbol type = decls->nth(i)->getType();

            if(callTbl.find(name) != callTbl.end() )
            {
                semant_error(decls->nth(i)) << "Function " << name << " was previously defined.\n";
            }
            else if(!isValidCallName(name))
            {
                semant_error(decls->nth(i)) << "FUnction name should not be 'printf'\n";
            }
            else
            {callTbl[name] = decls->nth(i);}
            
        }
    }
}

static void install_globalVars(Decls decls) {
    objectEnv.enterscope();

    for(int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        if( !(decls->nth(i)->isCallDecl()) )
        {
            Symbol name = decls->nth(i)->getName();
            Symbol type = decls->nth(i)->getType();

            if(!isValidTypeName(type))
            {
                semant_error(decls->nth(i)) << "Variable type should not be Void.\n";
            }
            else if(objectEnv.probe(name) != NULL)
            {
                semant_error(decls->nth(i)) << "GlobleVar " << name << " was previously defined.\n";
            }
            objectEnv.addid(name, new Symbol(type));
            globalvarsTbl[name] = type;
        }
    }
}

static void check_calls(Decls decls) {
    for(int i = decls->first(); decls->more(i); i = decls->next(i))
    {
        if(decls->nth(i)->isCallDecl())
        {
            decls->nth(i)->check();
        }
    }
}

static void check_main() {
    if(callTbl.find(Main) == callTbl.end())
    {
        //CallDecl_class* call_main = static_cast<CallDecl_class*>(callTbl[Main]);
        semant_error() << "Function Main was not defined.\n";
    }
    else
    {
        CallDecl_class* call_main = static_cast<CallDecl_class*>(callTbl[Main]);
        //理解强转的作用
        if(call_main->getType() != Void)
        {
            semant_error(callTbl[Main]) << "Main function should return Void.\n";
        }
        if(call_main->getVariables()->len() != 0)
        {
            semant_error(callTbl[Main]) << "Main function should not have parameter.\n";
        }
    }
    
}

void VariableDecl_class::check() {
    if(this->getType() == Void)
    {
        semant_error(this) << "Var " <<this->getName() << " should not be Void.\n";
    }
    else if(objectEnv.probe(this->getName()) != NULL)
    {
        semant_error(this) << "Var " << this->getName() << " was previously defined.\n";
    }
    else
    {
        objectEnv.addid(this->getName(), new Symbol(this->getType()));
    }

}

//check break continue
/*void check_dataflow(Stmts stmts)
{
    for(int i = stmts->first(); stmts->more(i); i = stmts->next(i))
    {
        
        int stmtType = stmts->nth(i)->isWhatStmt();
        if(stmtType == 3)
        {
            continue;
        }
        else if(stmtType == 7)
        {
            "Break statement should be used in loop.\n";
        }
        else if(stmtType == 6)
        {
            "Continue statement should be used in loop.\n";
        }
        else if(stmtType == 1)
        {
            Stmts cccc = single_Stmts(stmts->nth(i));
            check_dataflow(cccc);
        }
    }
}
*/
void CallDecl_class::check() {
    objectEnv.enterscope();
    //check formal parameter list
    Variables varFormalList = this->getVariables();
    for(int i = varFormalList->first(); varFormalList->more(i); i = varFormalList->next(i))
    {
        if(varFormalList->nth(i)->getType() == Void)
        {
            semant_error(varFormalList->nth(i)) << "Void should not be the type of formal parameter.\n";
        }
        else if(objectEnv.probe(varFormalList->nth(i)->getName()) != NULL)
        {
            semant_error(varFormalList->nth(i)) << "Formal parameter should not be multiply defined.\n";
        }
        else if(varFormalList->len() > 6)
        {
            semant_error(varFormalList->nth(i)) << "Formal parameter should <= 6.\n";
        }
        else
        {
            objectEnv.addid(varFormalList->nth(i)->getName(), new Symbol(varFormalList->nth(i)->getType()));
        }
        
    }

    //check stmtblock
    StmtBlock stmtblock = this->getBody();
    stmtblock->check(returnType);

    //check returnType
    Symbol returnType = this->getType();
    Stmt lastStmt = stmtblock->getStmts()->nth(stmtblock->getStmts()->len() - 1);

    if(lastStmt->isWhatStmt() != 5)  //应该写个enum增加可读性的，但懒得写
    {
        semant_error(this) << "Function should have return statement.\n";
        return;
    }

    //dont forget
    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {
    objectEnv.enterscope();
    VariableDecls vars = this->getVariableDecls();
    Stmts stmts = this->getStmts();

    //check vars
    for(int i = vars->first(); vars->more(i); i = vars->next(i))
    {
        vars->nth(i)->check(); //is Void? is multi defined? then addin scope.             
    }

    //check stmts
    this->pass_single_stmt_flag();    
    for(int i = stmts->first(); stmts->more(i); i = stmts->next(i))
    {
        stmts->nth(i)->check(type);
    }

    objectEnv.exitscope();
}

void IfStmt_class::check(Symbol type) {
    //three part
    if(this->getCondition()->checkType() != Bool)
    {
        semant_error(this) << "Condition statement of 'if' should be Bool.\n"; 
    }

    this->getThen()->setFlag(this->getLoopFlag());
    this->getElse()->setFlag(this->getLoopFlag());
    this->getThen()->check(type);
    this->getElse()->check(type);
}

void WhileStmt_class::check(Symbol type) {
    Expr condition = this->getCondition();
    StmtBlock body = this->getBody();
    body->setFlag(true);

    if (condition->checkType() != Bool) {
        semant_error(this)<<"Condition statement of 'while' should be Bool.\n";
    }

    body->check(type);
}

void ForStmt_class::check(Symbol type) {
    Expr initex = this->getInit();
    Expr condition = this->getCondition();
    Expr loopex = this->getLoop();
    StmtBlock body = this->getBody();
    body->setFlag(true);

    //four part
    initex->checkType();
    loopex->checkType();
    if (condition->checkType() != Bool) {
        semant_error(this)<<"Condition statement of 'for' should be Bool.\n";
    }
    body->check(type);
}

void ReturnStmt_class::check(Symbol type) {
    this->getValue()->checkType();
    if(!sameType(type, this->getValue()->checkType()))
        {
            semant_error(this) << "Return statement do not return the same type as the declaration.\n";
        }
}

void ContinueStmt_class::check(Symbol type) {
    if(!this->getLoopFlag()){
        semant_error(this)<<"Continue Statement Must be Used in Loop"<<endl;
    }
}

void BreakStmt_class::check(Symbol type) {
    if(!this->getLoopFlag()){
        semant_error(this)<<"Break Statement Must be Used in Loop"<<endl;
    }
}

Symbol Call_class::checkType(){
    Symbol name = this->getName();
    Actuals actuals = this->getActuals();

    //print func
    if(name == print)
    {
        if(actuals->len() == 0)
        {
            semant_error(this) << "printf fuction should have at least one parameter.\n";
            this->setType(Void);
            return type;
        }
        else if(actuals->nth(actuals->first())->checkType() != String)
        {
            semant_error(this) << "The first parameter of printf function should be String.\n";
            this->setType(Void);
            return type;
        }

        this->setType(Void);
        return type;
    }      //other call, check name and actuals
    else if(callTbl.find(name) == callTbl.end())
    {
        semant_error(this) << "Function name " << name << " was not defined.\n";
        this->setType(Void);
        return type;
    }

    CallDecl_class* formalsDecl = static_cast<CallDecl_class*>(callTbl[name]);
    if(actuals->len() != formalsDecl->getVariables()->len())
    {
        semant_error(this) << "Actuals lengths != formals length.\n";
    }
    else 
    {
        for(int i = actuals->first(); actuals->more(i); i = actuals->next(i))
        {
            Symbol actualExprType = actuals->nth(i)->checkType();
            Symbol formalExprType = formalsDecl->getVariables()->nth(i)->getType();

            if(actualExprType != formalExprType)
            {
                semant_error(this) << "Actuals type != formals type.\n";
            }

            actuals->nth(i)->checkType();
        }
    }

    this->setType(callTbl[name]->getType());
    return type;

}

Symbol Actual_class::checkType(){
    this->setType(expr->checkType());
    return expr->checkType();
}

Symbol Assign_class::checkType(){
    Symbol rtype = value->checkType();
    Symbol ltype = *objectEnv.lookup(lvalue);

    if(objectEnv.lookup(lvalue) == NULL)
    {
        semant_error(this) << "Assign " << lvalue << " was not defined.\n";
        setType(Int);
        return type;
    }
    else if(!sameType(rtype, ltype))
    {
        semant_error(this) << "Right type != left type.\n";
        setType(Int);
        return type;
    }
    this->setType(ltype);
    return type;
}

Symbol Add_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Add should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else if(t1 == Int && t2 == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        setType(Float);
        return type;
    }
    
}

Symbol Minus_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Minus should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else if(t1 == Int && t2 == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        setType(Float);
        return type;
    }
 
}

Symbol Multi_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Multi should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else if(t1 == Int && t2 == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        setType(Float);
        return type;
    }
  
}

Symbol Divide_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Divide should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else if(t1 == Int && t2 == Int)
    {
        setType(Int);
        return type;
    }
    else
    {
        setType(Float);
        return type;
    }
 
}

Symbol Mod_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if(t1 != Int && t2 != Int)
    {
        semant_error(this) << "Mod should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Int);
        return type;
    }
    
}

Symbol Neg_class::checkType(){
    Symbol t1 = e1->checkType();

    if( t1 != Int && t1 != Float)
    {
        semant_error(this) << "Neg should not happen with " << t1 << " .\n";
        setType(Int);
        return type;
    }
    else if(t1 == Int )
    {
        setType(Int);
        return type;
    }
    else
    {
        setType(Float);
        return type;
    }
   
}

Symbol Lt_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol Le_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol Equ_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float && t1 != Bool) || (t2 != Int && t2 != Float && t2 != Bool) )
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else if( (t1 == t2) || (t1 == Int && t2 == Float) || (t1 == Float && t2 == Int) )
    {
        setType(Bool);
        return type; 
    }
    else
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
 
}

Symbol Neq_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float && t1 != Bool) || (t2 != Int && t2 != Float && t2 != Bool) )
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else if( (t1 == t2) || (t1 == Int && t2 == Float) || (t1 == Float && t2 == Int) )
    {
        setType(Bool);
        return type; 
    }
    else
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
 
}

Symbol Ge_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol Gt_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Int && t1 != Float) || (t2 != Int && t2 != Float) )
    {
        semant_error(this) << "Compare should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol And_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Bool) || (t2 != Bool) )
    {
        semant_error(this) << "And&& should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Bool);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol Or_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 != Bool) || (t2 != Bool) )
    {
        semant_error(this) << "Or|| should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol Xor_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if((t1 == Bool) && (t2 == Bool) )
    {
        setType(Bool);
        return type;
    }
    else if( (t1 == Int) && (t2 == Int)  )
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Xor^ should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }
    
}

Symbol Not_class::checkType(){
    Symbol t1 = e1->checkType();

    if( (t1 != Bool) )
    {
        semant_error(this) << "Not! should not happen with "<< t1 << ".\n";
        setType(Int);
        return type;
    }
    else
    {
        setType(Bool);
        return type;
    }
 
}

Symbol Bitand_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 == Int) && (t2 == Int)  )
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Bitand should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }

}

Symbol Bitor_class::checkType(){
    Symbol t1 = e1->checkType();
    Symbol t2 = e2->checkType();

    if( (t1 == Int) && (t2 == Int)  )
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Bitor should not happen between "<< t1 << " and " << t2 << ".\n";
        setType(Int);
        return type;
    }

}

Symbol Bitnot_class::checkType(){
    Symbol t1 = e1->checkType();

    if(t1 == Int )
    {
        setType(Int);
        return type;
    }
    else
    {
        semant_error(this) << "Bitnot should not happen with "<< ".\n";
        setType(Int);
        return type;
    }

}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if(objectEnv.lookup(var))
    {
        type = *objectEnv.lookup(var);
    }
    else
    {
        semant_error(this) << "Object " << var << " was not difined.\n";
        this->setType(Void);
        return type;
    }
    this->setType(type);
    return type;
    
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



