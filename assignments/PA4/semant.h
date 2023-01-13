#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>
#include <sstream>
#include <map>
#include <vector>
#include <string>
#include <utility>
#include "cool-tree.h"  
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define __MY_DEBUG__

#define TRUE 1
#define FALSE 0

#define __BREAKABLE__ }switch(0){default:

using std::stringstream;
using std::map;
using std::vector;
using std::string;
using std::pair;

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

// type tree, also called inheritence tree, records partial order of types
// type nodes constitute a type tree
// (every class name is also a type; SELF_TYPE is another type which is
// treated specially, so not recorded explicitly in type tree)
class TypeNode {
private:
  Class_    c;
  Symbol    type;
  TypeNode  *parent;
  vector<TypeNode *> children;

public:
  TypeNode(Class_ c, Symbol cur_type, TypeNode *parent);
  Class_   get_class();
  Symbol   get_type();
  TypeNode *get_parent();
  vector<TypeNode *>& get_children();
  void add_child(TypeNode *child);
  void update_parent(TypeNode *parent);
};

class ClassTable {
private:
  int semant_errors;
  ostream& error_stream;
  TypeNode *type_tree_root;
  map<char *, TypeNode *> type_node_map; // used to find the node by Symbol name quickly

  // add a class (type) to the type tree by adding a TypeNode and update its parent
  // if a parent is not declared yet, also create a TypeNode for the parent
  // if current type exists, no need to add a TypeNode but update its parent ptr
  void add_class(Class_ c);
  void install_basic_classes();
  void check_acyclic_tree();
  bool find_cycle(TypeNode *node, map<TypeNode *, bool> vis_map, int depth = 0);

#ifdef __MY_DEBUG__
  void dump_type_node_map();
#endif

public:
  // iterate over classes to construct type tree, and hence the class table
  // if errors occur within this method, abort after the call
  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c, string error_msg);
  ostream& semant_error(Symbol filename, tree_node *t, string error_msg);
  
  // t1 <= t2 ? true : false
  bool is_subtype(Symbol t1, Symbol t2, 
                  bool self_type1 = false, bool self_type2 = false);
  // find least upper bound in the type tree
  Symbol lub(Symbol t1, Symbol t2, 
             bool self_type1 = false, bool self_type2 = false);
  // find the type of a class
  Symbol find(Symbol t) 
};

/* 
  MethodTable defines a method mapping M(f,C)=[T0,T1,...,TN,T(N+1)],
  where f = method name, C = class name, Ti (i<=N) = formal type,
  T(N+1) = return type
  Signature defines Ti (i<=N+1)
*/
typedef vector<Symbol> Symbols;

class Signature {
private:
  Symbols &formal_list;
  Symbol         return_type;
public:
  Signature(Symbols &formal_list, Symbol return_type) : 
    formal_list(formal_list), return_type(return_type) { }
  Symbols &get_formal_types() { return formal_list; }
  Symbol get_return_type() { return return_type; }
  string to_string() {
    stringstream ss;
    for (auto &sym : formal_list) {
      ss << sym << ',';
    }
    ss << return_type;
    return ss.str();
  }
};

class MethodTable {
private:
  map<pair<char *, char *>, Signature *> m;
public:
  MethodTable() { };
  Signature *get(char *func_name, char *class_name);
  void set(char *func_name, char *class_name, Signature *sig);
  bool has_key(char *func_name, char *class_name);

#ifdef __MY_DEBUG__
  void dump();
#endif
};

class Environment {
public:
  ClassTable                  *CT;
  SymbolTable<char *, Symbol> *O;
  MethodTable                 *M;
  Class_                      C;

  Environment(ClassTable *ct, SymbolTable<char *, Symbol> *o,
              MethodTable *m, Class_ c) : CT(ct), O(o), M(m), C(c) { }
};


#endif

