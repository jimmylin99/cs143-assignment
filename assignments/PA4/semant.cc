/*
 * Though passed all tests provided in the grading script,
 * I believe this semantic analyzer exist bugs which is not
 * caught by the grader. Even if I think these bugs may not
 * be too problematic, their existence (or say my lack of
 * confidence) shows some potential design flaws.
 *
 * Overall, the design is acceptable by myself, but the
 * details remain more consideration. It is also difficult
 * to write elegant and performative codes with provided
 * packages (e.g. hard to compare and find symbols by name).
 * I tried not to blame to it, so all codes does not modify
 * these packages and manage to conform to this design
 * pattern. This assignment is more competitive than previous
 * two, and I receive more sense of achievement when receiving
 * 74 out of 74.
 *
 * A scary but important story: I accidentally
 * rm -rf /usr/class/cool
 * but the directory I am working on (~/cool) is a soft link
 * to the one I deleted. Besides, I did not git push the code
 * I have written. Then, I lost codes written for a week.
 * Luckily I use R-Linux to recover my data with the help
 * of my Windows installed on my dual boost laptop.
 * This alerts me that optimizing workflow is essential, and
 * I turned to use replace command rm with trash.
 * Hope this will remind you of data safety.
 *
 * Jimmy Lin
 */

#include <typeinfo>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <queue>
#include <utility>
#include <fmt/format.h>
#include "semant.h"
#include "utilities.h"

using fmt::format;
using std::queue;
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

//////////////////////////////////////////////////////////////////////////////
// symbol utilities
//////////////////////////////////////////////////////////////////////////////
// guarantee that both are not nullptr!
bool equal_symbol(Symbol a, Symbol b) {
    return a->equal_string(b->get_string(), b->get_len());
}

bool is_self_type(Symbol s) {
    return s->equal_string(SELF_TYPE->get_string(), SELF_TYPE->get_len());
}

/*
 * I introduce an auxiliary type: ST type, to incorporate SELF_TYPE and
 * its subscript into one Symbol. This design conforms to the one Symbol
 * design for type (there is no need to add parameters to related methods)
 *
 * Technically, SELF_TYPE occurred in class C (i.e. SELF_TYPE with
 * subscript C) will become _SELF_TYPE_C. As no valid symbols can start
 * with underscore _, this composition will not pollute the symbol pool.
 *
 * However, this technique will lead to inconsistency to type interface
 * provided by the assignment. Specifically, the lab asks me to call
 * Expression::set_type(Symbol s), while if it is a SELF_TYPE, I should
 * not pass its ST type to it. Therefore, I have to pack the transform
 * (i.e. remove the prefix to convert the ST type back to the type
 * accepted by the grading script) in the set_type method, which
 * nevertheless intrude the file cool-tree.handcode.h. Though the manual
 * does not allow this modification explicitly, it does not disallow it.
 * In addition, when I need to retrieve the type, I have to distinguish
 * whether I need the original type or the ST type. The reason why I
 * have to keep the original type is that the type interface does not
 * accept customized type format.
 *
 * Overall, this design is used to alleviate programming difficulty,
 * and conform to provided interfaces.
 *
 */

bool is_compacted_ST(Symbol s) {
    if (s->get_len() <= strlen("_SELF_TYPE_"))
        return false;
    char *prefix_s = new char[12];
    strncpy(prefix_s, s->get_string(), 11);
    prefix_s[11] = '\0';
    return strcmp(prefix_s, "_SELF_TYPE_") == 0;
}

char *get_baseST(Symbol s) {
    char *packedST = s->get_string();
    char *base = new char[s->get_len()];
    strcpy(base, packedST+11);
    return base;
}

Symbol compactST(char *c) {
    char *ST = new char[strlen(c) + 12];
    strcpy(ST, "_SELF_TYPE_");
    strcpy(ST+11, c);
    Symbol compactedST = idtable.add_string(ST);
    return compactedST;
}

Symbol compactST(Symbol c) {
    return compactST(c->get_string());
}

// formalize ST
//   convert an ST type to an original-styled type by removing redundant prefix
Symbol fmlST(Symbol s) {
    if (is_compacted_ST(s))
        return SELF_TYPE;
    return s;
}

//
bool is_subset_symbol(Symbol a, Symbols b_list) {
    for (auto &elem : b_list) {
        if (equal_symbol(a, elem))
            return true;
    }
    return false;
}

//
Expression Expression_class::set_type(Symbol s) {
    type = fmlST(s);
    ST_type = s;
    return this;
}

void Case_class::set_type(Symbol s) {
    type = fmlST(s);
    ST_type = s;
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

void TypeNode::update_class(Class_ c) {
    this->c = c;
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
    check_acyclic_tree();
}

////////////////////////////////////////////////////////////////////
// private methods of ClassTable

void ClassTable::add_class(Class_ c) {
    Symbol cSymbol = c->get_name();
    Symbol pSymbol = c->get_parent();

    if (equal_symbol(cSymbol, SELF_TYPE)) {
        semant_error(c, "Redefinition of basic class SELF_TYPE.");
        return;
    }

    if (equal_symbol(pSymbol, SELF_TYPE)) {
        semant_error(c, format("Class {} cannot inherit class SELF_TYPE.", cSymbol->get_string()));
        return;
    }

    if (is_subset_symbol(pSymbol, Symbols{Int, Bool, Str})) {
        semant_error(c, format("Class {} cannot inherit {}.", cSymbol->get_string(), pSymbol->get_string()));
        return;
    }

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
        pNode = new TypeNode(nullptr, pSymbol, NULL);
        type_node_map[pSymbol->get_string()] = pNode;
    }

    if (cNode == NULL) {
        cNode = new TypeNode(c, cSymbol, pNode);
        type_node_map[cSymbol->get_string()] = cNode;
    } else {
        cNode->update_parent(pNode);
        cNode->update_class(c);
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
        char *type_name = it->first;
        TypeNode *node = it->second; // it->second?->get_class()

        if (strcmp(type_name, No_class->get_string()) == 0)
            continue;
        if (node == nullptr || node->get_parent() == nullptr) {
            assert(0); // impossible
            continue;
        }
        // other than Object (and No_class), if one's parent does not define property class, abort
        if (strcmp(type_name, Object->get_string()) != 0 &&
            node->get_parent()->get_class() == nullptr) {
            // error: handling node, meaning the class is not defined, abort
            semant_error(node->get_class(),
                         format("Class {} is not defined.",
                                node->get_parent()->get_type()->get_string()));
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

// get root node
TypeNode *ClassTable::get_root() { return type_tree_root; }

#ifdef __MY_DUMP_FUNCS__
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

// check if type1 <= type2
bool ClassTable::is_subtype(Symbol type1, Symbol type2) {
    bool self_type1 = is_compacted_ST(type1);
    bool self_type2 = is_compacted_ST(type2);
    char *t1 = (self_type1 ? get_baseST(type1) : type1->get_string());
    char *t2 = (self_type2 ? get_baseST(type2) : type2->get_string());
    // SELF_TYPE_x <= SELF_TYPE_x
    if (self_type1 && self_type2) {
        assert(strcmp(t1, t2) == 0);
        return true;
    }
    // C <= SELF_TYPE_x will never hold
    if (self_type2) {
        return false;
    }
    // SELF_TYPE_c <= P if C <= P, follow normal logic
    TypeNode *n1 = type_node_map[t1];
    while (n1 != NULL) {
        if (n1->get_type()->equal_string(
            t2, strlen(t2)
        ))
            return true;
        n1 = n1->get_parent();
    };
    return false;
}

// find least upper bound of two classes
Symbol ClassTable::lub(Symbol type1, Symbol type2) {
    bool self_type1 = is_compacted_ST(type1);
    bool self_type2 = is_compacted_ST(type2);
    char *t1 = (self_type1 ? get_baseST(type1) : type1->get_string());
    char *t2 = (self_type2 ? get_baseST(type2) : type2->get_string());
    // SELF_TYPE does not affect lub operation
    map<TypeNode *, bool> vis;
    TypeNode *n1 = type_node_map[t1];
    while (n1 != NULL) {
        vis[n1] = true;
        n1 = n1->get_parent();
    };
    TypeNode *n2 = type_node_map[t2];
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
// definition of Signature
bool Signature::equals(const Signature &sig) const {
    if (formal_list->size() != sig.formal_list->size())
        return false;
    for (int i = 0; i < formal_list->size(); ++i)
        if (!equal_symbol((*formal_list)[i], (*sig.formal_list)[i]))
            return false;
    return equal_symbol(return_type, sig.return_type);
}
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

#ifdef __MY_DUMP_FUNCS__
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


// an implementation of safe idtable.lookup, but the program will not fail if we cannot find the key
// but with poor efficiency (may be O(N^2) due to stringtab implementation)
Symbol safe_idtable_lookup_string(char *str) {
    // iterate over idtable entries
    for (int i = idtable.first(); idtable.more(i); i = idtable.next(i)) {
        auto sym = idtable.lookup(i);
        if (sym->equal_string(str, strlen(str)))
            return sym;
    }
    return nullptr;
}

void check_case(Environment *env, Case expr);

/*
 * check types of expression (also perform inference), following
 * instructions in cool-manual.pdf section 12.
 *
 * this is the major part of type checking, the rest are done in
 * semant() (for methods and attributes) and in check_case
 *
 */
void check_expr(Environment *env, Expression expr) {
    if (semant_debug) {
    cout << "check_expr " << env->C->get_name()->get_string() << " "
         << typeid(*expr).name() << endl;
    }

    char *class_name = env->C->get_name()->get_string();
    
    env->O->enterscope();

    { __BREAKABLE__
        char *class_name = env->C->get_name()->get_string();
        // no_expr
        if (typeid(*expr) == typeid(no_expr_class)) {
            expr->set_type(No_type);
        }

        // assign
        if (typeid(*expr) == typeid(assign_class)) {
            auto sub_expr = expr->get_expr();
            check_expr(env, sub_expr);
            Symbol lsym = expr->get_name();
            if (equal_symbol(lsym, self)) {
                semant_error(cerr, env->C, expr,
                             format("Cannot assign to 'self'."
                             ));
                expr->set_type(Object);
                break;
            }
            Symbol T = *(env->O->lookup(lsym->get_string()));
            if (T == NULL) {
                semant_error(cerr, env->C, expr, 
                    format("Variable {} is not defined.",
                        expr->get_name()->get_string()
                ));
                expr->set_type(Object);
                break;
            }
            Symbol Tp = sub_expr->get_ST_type();
            if (!env->CT->is_subtype(Tp, T)) {
                semant_error(cerr, env->C, expr, 
                    format("Inferred type {} of initialization of attribute \
{} does not conform to declared type {}.",
                           fmlST(Tp)->get_string(), expr->get_name()->get_string(), fmlST(T)->get_string()
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

        // dispatch & static_dispatch_class
        if (typeid(*expr) == typeid(dispatch_class) ||
            typeid(*expr) == typeid(static_dispatch_class)) {
            Expression e0 = expr->get_expr();
            check_expr(env, e0);
            Symbol T0 = e0->get_ST_type();

            char *func_name = expr->get_name()->get_string();
            // determine caller inferred type (in static dispatch, T0p is T)
            Symbol T0p = T0;
            if (typeid(*expr) == typeid(dispatch_class)) {
                if (is_compacted_ST(T0)) {
                    T0p = env->C->get_name();
                }
            } else if (typeid(*expr) == typeid(static_dispatch_class)) {
                Symbol type_name = expr->get_type_name();
                Symbol type = env->CT->find(type_name);
                if (type == nullptr) {
                    semant_error(cerr, env->C, expr,
                                 format("Static dispatch to undefined class {}.",
                                        type_name->get_string()
                                 ));
                    expr->set_type(Object);
                    break;
                }
                if (!env->CT->is_subtype(T0, type)) {
                    semant_error(cerr, env->C, expr,
                                 format("static type {} is not conform to \
the declared type of {}",
                                        fmlST(T0)->get_string(), fmlST(type_name)->get_string()
                    ));
                    expr->set_type(Object);
                    break;
                }
                T0p = type;
            } else { assert(0); }

            char *dispatch_class_name = T0p->get_string();
            Signature *sig = env->M->get(func_name, dispatch_class_name);
            if (sig == nullptr) {
                semant_error(cerr, env->C, expr,
                     format("Dispatch to undefined method {}.",
                            func_name
                ));
                expr->set_type(No_type);
                break;
            }
            Symbols arg_types = *(sig->get_formal_types()); // (T1',...,Tn')
            Symbol TRp = sig->get_return_type(); // T_{n+1}'
            // set T_{n+1}
            Symbol TR = TRp;
            if (is_self_type(TRp)) {
                TR = T0;
            }
            Expressions actual = expr->get_actual();
            bool pass_flag = true;
            if (actual->len() != arg_types.size()) {
                semant_error(cerr, env->C, expr,
                     format("Method {} called with wrong number of arguments.",
                            func_name
                 ));
                pass_flag = false;
            }
            for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
                if (!pass_flag) continue;
                Expression ei = actual->nth(i);
                check_expr(env, ei);
                Symbol Ti = ei->get_ST_type();

                Symbol Tip = arg_types[i];
                // check Ti <= Ti' (i <= n)
                if (!env->CT->is_subtype(Ti, Tip)) {
                    semant_error(cerr, env->C, expr, 
                        format("{}-th argument's inferred type {} is not conform to \
the declared type of {}",
                            i+1, fmlST(Ti)->get_string(), fmlST(Tip)->get_string()
                    ));
                    pass_flag = false;
                }
            }
            if (!pass_flag) {
                TR = Object;
            }
            expr->set_type(idtable.add_string(TR->get_string()));
        }

        // typcase
        if (typeid(*expr) == typeid(typcase_class)) {
            Expression e0 = expr->get_expr();
            check_expr(env, e0);
            Symbol T0 = e0->get_ST_type();

            Cases cases = expr->get_cases();
            if (cases->len() == 0) {
                semant_error(cerr, env->C, expr,
                             format("Case has no branch."
                             ));
                expr->set_type(Object);
                break;
            }
            map<char *, bool, cmp_str> branch_idtype_map;
            vector <Symbol> Tis;
            for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
                Case branch = cases->nth(i);
                env->O->enterscope();
                Symbol xi = branch->get_name();
                Symbol type_name = branch->get_type_decl();
                Symbol type = env->CT->find(type_name);
                if (type == nullptr) {
                    semant_error(cerr, env->C, expr,
                                 format("Branch type to undefined class {}.",
                                        type_name->get_string()
                                 ));
                    env->O->addid(xi->get_string(), new Symbol(Object));
                } else {
                    env->O->addid(xi->get_string(), new Symbol(type));
                    if (branch_idtype_map[type->get_string()]) {
                        semant_error(cerr, env->C, expr,
                                     format("Duplicate branch {} in case statement.",
                                            type->get_string()
                                     ));
                    }
                    branch_idtype_map[type->get_string()] = true;
                }
                check_case(env, branch);
                Tis.emplace_back(branch->get_ST_type());
                env->O->exitscope();
            }
            Symbol TR = Tis[0];
            for (int i = 1; i < Tis.size(); ++i) {
                TR = env->CT->lub(TR, Tis[i]);
            }
            expr->set_type(TR);
        }

        // block
        if (typeid(*expr) == typeid(block_class)) {
            Expressions body = expr->get_body();
            int i;
            for (i = body->first(); body->more(i); i = body->next(i)) {
                Expression ei = body->nth(i);
                check_expr(env, ei);
            }
            Expression en = body->nth(i-1);
            expr->set_type(en->get_ST_type());
        }

        // cond
        if (typeid(*expr) == typeid(cond_class)) {
            Expression pred = expr->get_pred();
            check_expr(env, pred);
            Symbol pred_type = pred->get_ST_type();
            if (!equal_symbol(pred_type, Bool)) {
                semant_error(cerr, env->C, expr,
                             format("pred is not a Bool type."));
                expr->set_type(Object);
                break;
            }

            Expression then_exp = expr->get_then_exp();
            Expression else_exp = expr->get_else_exp();
            check_expr(env, then_exp);
            check_expr(env, else_exp);
            Symbol T2 = then_exp->get_ST_type();
            Symbol T3 = else_exp->get_ST_type();
            Symbol TR = env->CT->lub(T2, T3);
            expr->set_type(TR);
        }

        // let
        if (typeid(*expr) == typeid(let_class)) {
            Symbol id = expr->get_identifier();
            if (equal_symbol(id, self)) {
                semant_error(cerr, env->C, expr,
                             format("'self' cannot be bound in a 'let' expression."));
                expr->set_type(Object);
                break;
            }
            Symbol type_name = expr->get_type_decl();
            Symbol type = env->CT->find(type_name);
            if (equal_symbol(type_name, SELF_TYPE))
                type = SELF_TYPE;
            if (type == nullptr) {
                semant_error(cerr, env->C, expr,
                             format("Let identifier type to undefined class {}.",
                                    type_name->get_string()
                             ));
                expr->set_type(Object);
                break;
            }
            Symbol T0p = type;
            if (is_self_type(type)) {
                T0p = compactST(class_name);
            }
            Expression init = expr->get_init();
            check_expr(env, init);
            // Let-Init
            if (!equal_symbol(init->get_ST_type(), No_type)) {
                Symbol T1 = init->get_ST_type();
                if (!env->CT->is_subtype(T1, T0p)) {
                    semant_error(cerr, env->C, expr,
                                 format("init type {} in let is not conform to \
the declared type of {}",
                                        fmlST(T0p)->get_string(), fmlST(T1)->get_string()
                                 ));
                    expr->set_type(Object);
                    break;
                }
            }
            env->O->enterscope();
            env->O->addid(id->get_string(), new Symbol(T0p));
            Expression body = expr->get_let_body();
            check_expr(env, body);
            Symbol TR = body->get_ST_type();
            expr->set_type(TR);
            env->O->exitscope();
        }

        // loop
        if (typeid(*expr) == typeid(loop_class)) {
            Expression pred = expr->get_pred();
            check_expr(env, pred);
            Symbol pred_type = pred->get_ST_type();
            Expression body = expr->get_loop_body();
            if (!equal_symbol(pred_type, Bool)) {
                semant_error(cerr, env->C, expr,
                             format("pred is not a Bool type."));
                expr->set_type(Object);
                break;
            }
            check_expr(env, body);
            expr->set_type(Object);
        }

        // isvoid
        if (typeid(*expr) == typeid(isvoid_class)) {
            Expression e1 = expr->get_e1();
            check_expr(env, e1);
            expr->set_type(Bool);
        }

        // comp (not expr)
        if (typeid(*expr) == typeid(comp_class)) {
            Expression e1 = expr->get_e1();
            check_expr(env, e1);
            Symbol e1_type = e1->get_ST_type();
            if (!equal_symbol(e1_type, Bool)) {
                semant_error(cerr, env->C, expr,
                             format("Operand of not is not a Bool type."));
                expr->set_type(Object);
                break;
            }
            expr->set_type(Bool);
        }

        // neg (~expr)
        if (typeid(*expr) == typeid(neg_class)) {
            Expression e1 = expr->get_e1();
            check_expr(env, e1);
            Symbol e1_type = e1->get_ST_type();
            if (!equal_symbol(e1_type, Int)) {
                semant_error(cerr, env->C, expr,
                             format("Operand of neg is not a Int type."));
                expr->set_type(Object);
                break;
            }
            expr->set_type(Int);
        }

        // compare (<, <=)
        if (typeid(*expr) == typeid(lt_class) ||
            typeid(*expr) == typeid(leq_class)) {
            Expression e1 = expr->get_e1();
            check_expr(env, e1);
            Symbol e1_type = e1->get_ST_type();
            if (!equal_symbol(e1_type, Int)) {
                semant_error(cerr, env->C, expr,
                             format("Operand of compare is not a Int type."));
                expr->set_type(Object);
                break;
            }

            Expression e2 = expr->get_e2();
            check_expr(env, e2);
            Symbol e2_type = e2->get_ST_type();
            if (!equal_symbol(e2_type, Int)) {
                semant_error(cerr, env->C, expr,
                             format("Operand of compare is not a Int type."));
                expr->set_type(Object);
                break;
            }
            expr->set_type(Bool);
        }

        // arith (+, -, *, /)
        if (typeid(*expr) == typeid(plus_class) ||
            typeid(*expr) == typeid(sub_class) ||
            typeid(*expr) == typeid(mul_class) ||
            typeid(*expr) == typeid(divide_class)) {
            Expression e1 = expr->get_e1();
            check_expr(env, e1);
            Symbol e1_type = e1->get_ST_type();
            if (!equal_symbol(e1_type, Int)) {
                semant_error(cerr, env->C, expr,
                             format("Operand of arith is not a Int type."));
                expr->set_type(Object);
                break;
            }

            Expression e2 = expr->get_e2();
            check_expr(env, e2);
            Symbol e2_type = e2->get_ST_type();
            if (!equal_symbol(e2_type, Int)) {
                semant_error(cerr, env->C, expr,
                             format("Operand of arith is not a Int type."));
                expr->set_type(Object);
                break;
            }
            expr->set_type(Int);
        }

        // equal (=)
        if (typeid(*expr) == typeid(eq_class)) {
            Expression e1 = expr->get_e1();
            check_expr(env, e1);
            Symbol e1_type = e1->get_ST_type();

            Expression e2 = expr->get_e2();
            check_expr(env, e2);
            Symbol e2_type = e2->get_ST_type();

            if (is_subset_symbol(e1_type, Symbols{Int, Str, Bool}) ||
                    is_subset_symbol(e2_type, Symbols{Int, Str, Bool})) {
                if (!equal_symbol(e1_type, e2_type)) {
                    semant_error(cerr, env->C, expr,
                                 format("Operand of equal with either in basic type does not match the other."));
                    expr->set_type(Object);
                    break;
                }
            }
            expr->set_type(Bool);
        }

        // new_
        if (typeid(*expr) == typeid(new__class)) {
            Symbol type_name = expr->get_type_name();
            Symbol type = env->CT->find(type_name);

            if (type == nullptr && !equal_symbol(type_name, SELF_TYPE)) {
                semant_error(cerr, env->C, expr, 
                    format("'new' used with undefined class {}.",
                        type_name->get_string()
                ));
                expr->set_type(Object);
                break;
            }
            if (is_self_type(type_name)) {
                expr->set_type(idtable.add_string(compactST(class_name)->get_string()));
            } else {
                expr->set_type(idtable.add_string(type->get_string()));
            }
        }

        // object
        if (typeid(*expr) == typeid(object_class)) {
            Symbol sym = safe_idtable_lookup_string(expr->get_name()->get_string());

            Symbol *TPtr = env->O->lookup(sym->get_string());
            if (TPtr == nullptr || sym == nullptr) {
                semant_error(cerr, env->C, expr, 
                    format("Variable {} is not defined.",
                        expr->get_name()->get_string()
                ));
                expr->set_type(No_type);
                break;
            }
            expr->set_type(*TPtr);
        }
    }

    env->O->exitscope();
}

void check_case(Environment *env, Case expr) {
    {__BREAKABLE__
            // branch
            if (typeid(*expr) == typeid(branch_class)) {
                Symbol name = expr->get_name();
                Symbol type_name = expr->get_type_decl();

                Expression sub_expr = expr->get_expr();
                check_expr(env, sub_expr);
                expr->set_type(sub_expr->get_ST_type());
            }
    }
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

    /*
     * two auxiliary data structures, used to store temporary table for
     * attributes (OC) and methods (temp_method_map).
     *
     * technically, they will be used by current class to inherit parent's
     * elements, and perform some checks based on its facility to search
     * elements (that is why I use map).
     */
    // key: class_name, value: map<idname:char *, type:Symbol>
    // O_c, used for attribute inheritance
    map<char *, map<char *, Symbol, cmp_str>, cmp_str> OC;
    // key: class_name, value: vector<pair<func_name:char *, sig:Signature *>>
    map<char *, vector<pair<char *, Signature *>>> temp_method_map;

    /* traverse AST */
    /*
     * glean information for method table & symbol table using BFS
     *
     * I choose to use BFS because inheritance depends on child-parent
     * relation. When comparing with DFS, BFS is easier to organize
     * existing codes. Of course, there exists some alternatives like
     * giving an order to the class TypeNode's in advance, while it
     * may introduce more methods.
    */
    queue<TypeNode *> q;
    q.emplace(classtable->get_root());
    while (!q.empty()) {
        TypeNode *topNode = q.front();
        Class_ c = topNode->get_class();
        q.pop();
        for (auto child : topNode->get_children()) {
            q.emplace(child);
        }
        if (c == nullptr) {
            continue; // ignore further ops for No_class
        }

        char *class_name = c->get_name()->get_string();

        // inherit parent attributes (use temporary OC) && parent methods (use temporary method table to update global method table)
        if (topNode->get_parent() != nullptr) {
            Class_ pc = topNode->get_parent()->get_class();
            if (pc != nullptr) {
                char *pc_name = pc->get_name()->get_string();
                // attributes
                map<char *, Symbol, cmp_str> p_attr_sym_map = OC[pc_name];
                for (auto &pair_: p_attr_sym_map)
                    OC[class_name][pair_.first] = pair_.second;
                // methods
                for (auto &elem: temp_method_map[pc_name]) {
                    methodtable->set(elem.first, class_name, elem.second);
                    temp_method_map[class_name].emplace_back(elem);
                }
            }
        }

        Features features = c->get_features();
        auto attrMap = map<char *, bool>();
        for (int j = features->first(); features->more(j); j = features->next(j)) {
            Feature f = features->nth(j);
            // methods: build method table
            if (typeid(*f) == typeid(method_class)) {
                Formals formals = f->get_formals();
                Symbols *formal_types = new Symbols;
                for (int k = formals->first(); formals->more(k); k = formals->next(k)) {
                    Formal formal = formals->nth(k);
                    formal_types->emplace_back(formal->get_type_decl());
                    if (equal_symbol(formal->get_name(), self)) {
                        semant_error(cerr, c, f,
                                     format("'self' cannot be a formal name"
                                     ));
                        continue;
                    }
                }
                auto *newSig = new Signature(formal_types, f->get_return_type());
                // check if the method is already declared in this class
                char *func_name  = f->get_name()->get_string();
                if (methodtable->has_key(func_name, class_name)) {
                    auto *p_sig = methodtable->get(func_name, class_name);
                    if (!p_sig->equals(*newSig)) {
                        semant_error(cerr, c, f,
                                     format("Method {} is multiply defined in class.",
                                            f->get_name()->get_string()
                                     ));
                        continue;
                    }
                }
                // add method to the table
                methodtable->set(
                    func_name,
                    class_name,
                    newSig
                );
                temp_method_map[class_name].emplace_back(make_pair(
                    func_name,
                    newSig
                ));
                // add method to idtable
                idtable.add_string(func_name);
            }
            // attrs: check multi-definition & collect attributes id-symbol pairs
            if (typeid(*f) == typeid(attr_class)) {
                char *attr_name = f->get_name()->get_string();
                if (strcmp(attr_name, self->get_string()) == 0) {
                    semant_error(cerr, c, f,
                                 format("'self' cannot be the name of an attribute."
                                 ));
                    continue;
                }
                if (OC[class_name][attr_name] != nullptr) {
                    semant_error(cerr, c, f,
                                 format("Attribute {} is an attribute of an inherited class.",
                                        attr_name
                                 ));
                    continue;
                }
                Symbol type = f->get_type_decl();
                if (attrMap[attr_name]) {
                    semant_error(cerr, c, f, 
                        format("Attribute {} is multiply defined in class.",
                            attr_name
                        ));
                    continue;
                }
                attrMap[attr_name] = true;
                OC[class_name][attr_name] = type;
            }
        }
    }

    if (!methodtable->has_key(main_meth->get_string(), Main->get_string())) {
        cerr << "Class Main is not defined." << endl;
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }

    /* type check and inference
     * iterate over classes
     * - construct environment
     * - build symbol table for class (though most of the work are done
     *      in previous section, there may exist some design flaws)
     * - check all features recursively (attrs & methods)
     *      - this will call check_expr(), which is a major part
     *          of type checking
    */
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        Class_ c = classes->nth(i);
        char *class_name = c->get_name()->get_string();
        auto env = new Environment(classtable, symboltable, methodtable, c);
        env->O->enterscope();
        // add inherited attributes (stored in OC which was collected in previous block)
        for (auto &elem : OC[class_name]) {
            env->O->addid(elem.first, new Symbol(elem.second));
        }

        Features features = c->get_features();
        for (int j = features->first(); features->more(j); j = features->next(j)) {
            Feature f = features->nth(j);
            // first, iterate over attrs to build symbol table for the class
            if (typeid(*f) == typeid(attr_class)) {
                char *attr_name = f->get_name()->get_string();
                // assign static type to the attribute
                Symbol *attr_type_ptr = new Symbol;
                *attr_type_ptr = f->get_type_decl();
                env->O->addid(attr_name, attr_type_ptr);
                // add attr name to idtable
                idtable.add_string(attr_name);
            }
        }
        for (int j = features->first(); features->more(j); j = features->next(j)) {
            Feature f = features->nth(j);
            // check attrs recursively
            if (typeid(*f) == typeid(attr_class)) {
                env->O->enterscope();
                env->O->addid(self->get_string(),
                              new Symbol(idtable.add_string(compactST(class_name)->get_string())));
                check_expr(env, f->get_init());
//                Symbol attr_ = f->get_name();
                Symbol T0 = f->get_type_decl();
                Symbol T1 = f->get_init()->get_ST_type();
                if (!equal_symbol(T1, No_type)) {
                    if (!env->CT->is_subtype(T1, T0)) {
                        semant_error(cerr, env->C, f,
                                     format("static type {} is not conform to \
the declared type of {}",
                                            fmlST(T0)->get_string(), fmlST(T1)->get_string()
                                     ));
                        env->O->exitscope();
                        continue;
                    }
                }
                env->O->exitscope();
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
                    Symbol *formal_type_ptr = new Symbol;
                    *formal_type_ptr = formal_type;
                    env->O->addid(idtable.add_string(formal_name)->get_string(),
                                  formal_type_ptr);
                }
                // check method body recursively
                env->O->addid(self->get_string(),
                              new Symbol(idtable.add_string(compactST(class_name)->get_string())));
                check_expr(env, f->get_expr());
                Symbol T0 = f->get_return_type();
                if (equal_symbol(T0, SELF_TYPE))
                    T0 = compactST(c->get_name());
                Symbol T1 = f->get_expr()->get_ST_type();
                if (!env->CT->is_subtype(T1, T0)) {
                    semant_error(cerr, env->C, f,
                                 format("static type {} is not conform to \
the declared type of {}",
                                        fmlST(T1)->get_string(), fmlST(T0)->get_string()
                                 ));
                }
                env->O->exitscope();
            }
        }
        env->O->exitscope();
    }

    if (error_cnt) {
	cerr << "Compilation halted due to static semantic errors." << endl;
    exit(1);
    }
}
