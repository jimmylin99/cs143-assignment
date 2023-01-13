

#include <typeinfo>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <utility>
#include <fmt/format.h>
#include "semant.h"
#include "utilities.h"

using fmt::format;
using std::make_pair;

extern int semant_debug;
extern char *curr_filename;

int error_cnt;

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
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

////////////////////////////////////////////////////////////////////
// definition of TypeNode

TypeNode::TypeNode(Class_ c, Symbol cur_type, TypeNode *parent) :
    c(c), type(cur_type), parent(parent), children() { }

Class_ TypeNode::get_class() { return c; }
Symbol TypeNode::get_type() { return type; }
TypeNode *TypeNode::get_parent() { return parent; }
vector<TypeNode *>& TypeNode::get_children() { return children; }

void TypeNode::add_child(TypeNode *child) {
    children.emplace_back(child);
}

void TypeNode::update_parent(TypeNode *parent) {
    this->parent = parent;
}

// end of definition of TypeNode
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
// definition of ClassTable

////////////////////////////////////////////////////////////////////
// constructor of ClassTable

ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
    type_tree_root = new TypeNode(nullptr, No_class, (TypeNode *) NULL);
    type_node_map[No_class->get_string()] = type_tree_root;

    install_basic_classes();

    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ c = classes->nth(i);
        add_class(c);
        if (errors() > 0) return;
        idtable.add_string(c->get_name()->get_string());
    }

    if (semant_debug) {
        dump_type_node_map();
    }

    check_acyclic_tree();
}

////////////////////////////////////////////////////////////////////
// private methods of ClassTable

void ClassTable::add_class(Class_ c) {
    Symbol cSymbol = c->get_name();
    Symbol pSymbol = c->get_parent();

    if (cSymbol->equal_string(pSymbol->get_string(), pSymbol->get_len())) {
        // error: a class cannot inherit itself, abort
        semant_error(c, format("Class {} cannot inherit itself.", cSymbol->get_string()));
        return;
    }

    TypeNode *cNode = type_node_map[cSymbol->get_string()];
    TypeNode *pNode = type_node_map[pSymbol->get_string()];

    if (cNode != NULL && cNode->get_parent() != NULL) {
        // error: multi-declaration, abort
        semant_error(c, format("Class {} declared more than once.", cSymbol->get_string()));
        return;
    }

    if (pNode == NULL) {
        pNode = new TypeNode(c, pSymbol, NULL);
        type_node_map[pSymbol->get_string()] = pNode;
    }

    if (cNode == NULL) {
        cNode = new TypeNode(c, cSymbol, pNode);
        type_node_map[cSymbol->get_string()] = cNode;
    } else {
        cNode->update_parent(pNode);
    }

    pNode->add_child(cNode);
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);
    
    // add theses classes to the class table in order
    add_class(Object_class);
    add_class(IO_class);
    add_class(Int_class);
    add_class(Bool_class);
    add_class(Str_class);
}

void ClassTable::check_acyclic_tree() {
    // first check if every node has a parent *except for the root*
    for (auto it = type_node_map.begin(); it != type_node_map.end(); ++it) {
        if (strcmp(it->first, No_class->get_string()) == 0)
            continue;
        if (it->second->get_parent() == NULL) {
            // error: handling node, meaning the class is not defined, abort
            semant_error(it->second->get_class(), 
                         format("Class {} is not defined.", 
                                it->second->get_type()->get_string()));
            return;
        }
    }

    // then starting from the root, check the graph has no cycle
    map<TypeNode *, bool> vis;
    if (find_cycle(type_tree_root, vis)) {
        return;
    }
}

// assume the root (i.e. No_type) has only one child, i.e. Object
bool ClassTable::find_cycle(TypeNode *node, map<TypeNode *, bool> vis, int depth) {
    if (semant_debug) {
        cout << pad(depth * 2) << node->get_type() << endl;
    }
    for (auto child : node->get_children()) {
        if (vis[child]) {
            // error: cycle occurred in the inheritance tree, abort
            semant_error(child->get_class(), format("Cycle exists in class inheritance tree."));
            return true; // find cycle, throw error
        }
        vis[child] = true;
        if (find_cycle(child, vis, depth+1) == true) {
            return true;
        }
        vis[child] = false;
    }

    return false;
}

#ifdef __MY_DEBUG__
void ClassTable::dump_type_node_map() {
    for (const auto& elem : type_node_map) {
        cout << elem.first << ": " << elem.second->get_type()->get_string() << "->"
                << (elem.second->get_parent() == NULL ? "NULL" : 
                elem.second->get_parent()->get_type()->get_string()) << endl;
    }
}
#endif

// end of private methods of ClassTable
////////////////////////////////////////////////////////////////////
// public methods of ClassTable

bool ClassTable::is_subtype(Symbol t1, Symbol t2, 
    bool self_type1, bool self_type2) {
    // SELF_TYPE_x <= SELF_TYPE_x
    if (self_type1 && self_type2) {
        assert(t1->equal_string(
            t2->get_string(),
            t2->get_len()
        ));
        return true;
    }
    // C <= SELF_TYPE_x will never hold
    if (self_type2) {
        return false;
    }
    // SELF_TYPE_c <= P if C <= P, follow normal logic
    TypeNode *n1 = type_node_map[t1->get_string()];
    while (n1 != NULL) {
        if (n1->get_type()->equal_string(
            t2->get_string(),
            t2->get_len()
        ))
            return true;
        n1 = n1->get_parent();
    };
    return false;
}

Symbol ClassTable::lub(Symbol t1, Symbol t2, 
    bool self_type1, bool self_type2) {
    // SELF_TYPE does not affect lub operation
    map<TypeNode *, bool> vis;
    TypeNode *n1 = type_node_map[t1->get_string()];
    while (n1 != NULL) {
        vis[n1] = true;
        n1 = n1->get_parent();
    };
    TypeNode *n2 = type_node_map[t2->get_string()];
    while (n2 != NULL) {
        if (vis[n2])
            return n2->get_type();
        n2 = n2->get_parent();
    };
    assert(0); // Impossible
}

Symbol ClassTable::find(Symbol t)  {
    TypeNode *node = type_node_map[t->get_string()];
    if (node == nullptr)
        return nullptr;
    return node->get_type();
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c, string error_msg)
{                                                             
    return semant_error(c->get_filename(),c,error_msg);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t, string error_msg)
{
    error_stream << filename << ":" << t->get_line_number() << ": " << error_msg << endl;
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

// end of public methods of ClassTable
////////////////////////////////////////////////////////////////////
// end of definition of ClassTable
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
// definition of MethodTable
////////////////////////////////////////////////////////////////////

Signature *MethodTable::get(char *func_name, char *class_name) {
    return m[make_pair(func_name, class_name)];
}

void MethodTable::set(char *func_name, char *class_name, Signature *sig) {
    m[make_pair(func_name, class_name)] = sig;
}

bool MethodTable::has_key(char *func_name, char *class_name) {
    return m.find(make_pair(func_name, class_name)) != m.end();
}

#ifdef __MY_DEBUG__
void MethodTable::dump() {
    for (const auto &elem: m) {
        char *func = elem.first.first;
        char *method = elem.first.second;
        Signature *sig = elem.second;
        cout << format("M({},{})=[{}]", func, method, sig->to_string()) << endl;
    }
}
#endif

// end of definition of MethodTable
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
// definition of utilities
ostream& semant_error(ostream& stream, Class_ c, tree_node *t, string error_msg)
{
    stream << c->get_filename() << ":" << t->get_line_number() << ": " << error_msg << endl;
    error_cnt ++;
    return stream;
}
// end of definition of utilities
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
// definition of global methods
void check_expr(Environment *env, Expression expr) {
    if (semant_debug) {
    cout << "check_expr " << env->C->get_name()->get_string() << " "
         << typeid(*expr).name() << endl;
    }
    
    env->O->enterscope();

    { __BREAKABLE__
        char *class_name = env->C->get_name()->get_string();
        // no_expr
        if (typeid(*expr) == typeid(no_expr_class)) {
            expr->set_type(No_type);
        }

        // assign
        if (typeid(*expr) == typeid(assign_class)) {
            check_expr(env, expr->get_expr());
            Symbol T = *(env->O->lookup(expr->get_name()->get_string()));
            if (T == NULL) {
                semant_error(cerr, env->C, expr, 
                    format("Variable {} is not defined.",
                        expr->get_name()->get_string()
                ));
                break;
            }
            Symbol Tp = expr->get_type();
            if (!env->CT->is_subtype(Tp, T)) {
                semant_error(cerr, env->C, expr, 
                    format("Inferred type {} of initialization of attribute \
{} does not conform to declared type {}.",
                        Tp->get_string(), expr->get_name()->get_string(), T->get_string()
                ));
                expr->set_type(Object);
            } else {
                expr->set_type(idtable.add_string(Tp->get_string()));
            }

        }

        // bool_const
        if (typeid(*expr) == typeid(bool_const_class)) {
            expr->set_type(Bool);
        }

        // int_const
        if (typeid(*expr) == typeid(int_const_class)) {
            expr->set_type(Int);
        }

        // string_const
        if (typeid(*expr) == typeid(string_const_class)) {
            expr->set_type(Str);
        }

        // dispatch
        if (typeid(*expr) == typeid(dispatch_class)) {
            Expression e0 = expr->get_expr();
            Symbol T0 = e0->get_type();
            
            char *func_name = expr->get_name()->get_string();
            Symbol T0p = T0;
            if (T0->equal_string(
                SELF_TYPE->get_string(),
                SELF_TYPE->get_len()
            )) {
                T0p = env->C->get_name();
            }
            Signature *sig = env->M->get(func_name, class_name);
            Symbols &arg_types = sig->get_formal_types(); // (T1',...,Tn')
            Symbol TRp = sig->get_return_type(); // T_{n+1}'
            // set T_{n+1}
            Symbol TR = TRp;
            if (TRp->equal_string(
                SELF_TYPE->get_string(),
                SELF_TYPE->get_len()
            )) {
                TR = T0;
            }

            Expressions actual = expr->get_actual();
            bool pass_flag = true;
            for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
                Expression ei = actual->nth(i);
                check_expr(env, ei);
                Symbol Ti = ei->get_type();

                Symbol Tip = arg_types[i];
                // check Ti <= Ti' (i <= n)
                if (!env->CT->is_subtype(Ti, Tip)) {
                    semant_error(cerr, env->C, expr, 
                        format("{}-th argument's inferred type {} is not conform to \
the declared type of {}",
                            i+1, Ti->get_string(), Tip->get_string()
                    ));
                    pass_flag = false;
                }
            }
            if (!pass_flag) {
                TR = Object;
            }
            expr->set_type(idtable.add_string(TR->get_string()));
        }

        // block
        if (typeid(*expr) == typeid(block_class)) {
            Expressions body = expr->get_body();
            int i;
            for (i = body->first(); body->more(i); i = body->next(i)) {
                Expression ei = body->nth(i);
                cout << i << endl;
                check_expr(env, ei);
            }
            cout << i - 1 << endl;
            Expression en = body->nth(i-1);
            expr->set_type(en->get_type());
        }

        // new_
        if (typeid(*expr) == typeid(new__class)) {
            Symbol type_name = expr->get_type_name();
            Symbol type = env->CT->find(type_name);
            if (type == nullptr) {
                semant_error(cerr, env->C, expr, 
                    format("'new' used with undefined class {}.",
                        type_name->get_string()
                ));
                expr->set_type(Object);
                break;
            }
            if (type_name->equal_string(
                SELF_TYPE->get_string(),
                SELF_TYPE->get_len()
            )) {
                expr->set_type(SELF_TYPE);
            } else {
                expr->set_type(idtable.add_string(type->get_string()));
            }
        }

        // object
        if (typeid(*expr) == typeid(object_class)) {
            Symbol *TPtr = env->O->lookup(expr->get_name()->get_string());
            if (TPtr == NULL) {
                cout << "object_class nothing for " 
                     << expr->get_name()->get_string() << endl;
                semant_error(cerr, env->C, expr, 
                    format("Variable {} is not defined.",
                        expr->get_name()->get_string()
                ));
                break;
            }
            cout << "object_class " << expr->get_name()->get_string()
                 << " " << (*TPtr)->get_string() << " for y: "
                //  << (*(env->O->lookup("y")))->get_string() 
                 << endl;
            char *x = "x";
            cout << strcmp(x, expr->get_name()->get_string()) << endl; // if equal, return 0
            cout << ((env->O->lookup(x) != nullptr) ? "Yes x\n" : "No x\n");
            cout << ((env->O->lookup(expr->get_name()->get_string()) != nullptr) ? "Yes x\n" : "No x\n");
            cout << ((env->O->lookup("x") != nullptr) ? "Yes x\n" : "No x\n");
            cout << ((env->O->lookup("y") != nullptr) ? "Yes y\n" : "No y\n");

            expr->set_type(*TPtr);
            env->O->dump();
        }
    }

    env->O->exitscope();
}
// end of definition of global methods
////////////////////////////////////////////////////////////////////

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    if (semant_debug) {
        dump_with_types(cout,0);
    }

    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }

    auto symboltable = new SymbolTable<char *, Symbol>();
    auto methodtable = new MethodTable();

    /* traverse AST */
    // glean information for methodtable & symbol table
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ c = classes->nth(i);
        char *class_name = c->get_name()->get_string();
        Features features = c->get_features();

        auto attrMap = map<char *, bool>();
        for (int j = features->first(); features->more(j); j = features->next(j)) {
            Feature f = features->nth(j);
            // methods: build method table
            if (typeid(*f) == typeid(method_class)) {
                Formals formals = f->get_formals();
                Symbols formal_types;
                for (int k = formals->first(); formals->more(k); k = formals->next(k)) {
                    Formal formal = formals->nth(k);
                    formal_types.emplace_back(formal->get_type_decl());
                }
                // check if the method is already declared in this class
                char *func_name  = f->get_name()->get_string();
                if (methodtable->has_key(func_name, class_name)) {
                    semant_error(cerr, c, f, 
                        format("Method {} is multiply defined in class.",
                            f->get_name()->get_string()
                        ));
                    continue;
                }
                // add method to the table
                methodtable->set(
                    func_name,
                    class_name,
                    new Signature(formal_types, f->get_return_type())
                );
                // add method to idtable
                idtable.add_string(func_name);
            }
            // attrs: check multi-definition
            if (typeid(*f) == typeid(attr_class)) {
                char *attr_name = f->get_name()->get_string();
                if (attrMap[attr_name]) {
                    semant_error(cerr, c, f, 
                        format("Attribute {} is multiply defined in class.",
                            attr_name
                        ));
                    continue;
                }
                attrMap[attr_name] = true;
            }
        }
    }
    if (semant_debug) {
        methodtable->dump();
    }

    // type check and inference
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ c = classes->nth(i);
        char * class_name = c->get_name()->get_string();
        auto env = new Environment(classtable, symboltable, methodtable, c);
        env->O->enterscope();
        Features features = c->get_features();
        for (int j = features->first(); features->more(j); j = features->next(j)) {
            Feature f = features->nth(j);
            // first, iterate over attrs to build symbol table for the class
            if (typeid(*f) == typeid(attr_class)) {
                char *attr_name = f->get_name()->get_string();
                if (env->O->probe(attr_name) != NULL) {
                    // checked in previous step
                    // semant_error(cerr, c, f, 
                    //     format("Attribute {} is already defined in class {}.",
                    //         attr_name, class_name
                    //     ));
                    continue;
                }
                // assign static type to the attribute
                Symbol attr_type = f->get_type_decl();
                env->O->addid(attr_name, &attr_type);
                // add attr name to idtable
                idtable.add_string(attr_name);
            }
        }
        for (int j = features->first(); features->more(j); j = features->next(j)) {
            Feature f = features->nth(j);
            // check attrs recursively
            if (typeid(*f) == typeid(attr_class)) {
                check_expr(env, f->get_init());
            }
            // check methods recursively
            if (typeid(*f) == typeid(method_class)) {
                env->O->enterscope();
                char *method_name = f->get_name()->get_string();
                Formals formals = f->get_formals();
                // add formals to symbol table
                for (int k = formals->first(); formals->more(k); k = formals->next(k)) {
                    Formal formal = formals->nth(k);
                    char *formal_name = formal->get_name()->get_string();
                    if (env->O->probe(formal_name) != NULL) {
                        semant_error(cerr, c, f, 
                        format("Formal {} is already defined in method {} of class {}.",
                            formal_name, method_name, class_name
                        ));
                        continue;
                    }
                    Symbol formal_type = formal->get_type_decl();
                    cout << "add formals to ST: " << formal_name << " "
                         << formal_type->get_string() << endl;
                    env->O->addid(formal_name, &formal_type);
                }
                // check method body recursively
                check_expr(env, f->get_expr());
                env->O->exitscope();
            }
        }
        env->O->exitscope();
    }
    



    if (error_cnt) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	cout.flush();
    cerr.flush();
    exit(1);
    }
}
