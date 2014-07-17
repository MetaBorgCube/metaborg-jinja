module Types

// Typing rules as defined by Figure 12 of the paper.
  
type rules
// Literals:
  True():  Boolean()
  False(): Boolean()
  Int(_):  Integer()
  Null():  NullType()
  Unit():  Void()
//  Addr(a): ClassRef(a) // Should point to the class pointed by _a_

relations
  define transitive <subclass:

type rules
  CDecl(name, Class(Some(e), _, _)):-
  where store name <subclass: e
  
  MDecl(ty, name, params*, body):-
    where ty => Arrow(ty*,rty)
  	  and params* : ty'*
  	  and ty'* == ty*
  	 else error "Mismatched types for parameters."  on params* 
  	  and body : ty'
  	  and ty' == rty
  	 else error "Mismatched types for body." on body 
  	
  Parameter(ty, _): ty

relations
  // Sub-typing rules
  ty1 <: ty2
  where ty1 == ty2
     or (ty1 == NullType() and ty2 => ClassRef(e))
     or ty1 <class: ty2
  
  ty1 <class: ty2
  where ty1 == ty2
     or (
             ty1 => ClassRef(ty1')
         and ty2 => ClassRef(ty2')
         and ty1' <subclass: ty2'
        )
        
type rules
  New(c): c
  
  Literal(c): ty
  where c : ty
  
  VarAccess(c): ty
  where definition of c : ty
  
  Cast(cl, var): ty
  where cl : ty
    and ty => ClassRef(cty)
    and var : ty'
    and ty' => ClassRef(vty)
    and cty <class: vty
     or vty <class: cty
  
  eq@Eq(e1, e2): Boolean()
  where e1 : t1
    and e2 : t2
    and ((
            t1 <: t2
         or t2 <: t1
        )
   else error "Incompatible types for comparison." on eq)
  
  Add(e1, e2): Integer()
  where e1 : Integer()
   else error "Expression is not an Integer." on e1
    and e2 : Integer()
   else error "Expression is not an Integer." on e2
  
  VarAssign(var, e): Void()
  where (not (var == VariableRef("this")))
   else error "Variable may not be 'this'." on var
    and e : t'
    and definition of var : t
    and t' <: t
   else error "Expression not of the proper type." on e
  
  FldAccess(e, fld, dcl): ty
  where definition of fld : ty
    and e : tye
    and tye <class: dcl
   else error "Field access class has to be a subtype of the object's class." on dcl
  
  FldAssign(e1, fld, dcl, e2): Void()
  where (
         definition of fld : t
         and e2 : tye2
         and tye2 <: t
        else error "Expression of the wrong type for the field." on e2
        )
    and (
             e1 : tye1
         and tye1 <class: dcl
        else error "Field access class has to be a subtype of the object's class." on dcl
        )
  
  MethodCall(e1, name, es*): rty
  where definition of name : Arrow(ty*, rty)
    and es* : ty'*
    and ty'* <: ty*
   else error "Incompatible error types." on es*
   
  Block(_, _, e): ty
  where e : ty
  
  Seq(e1, e2): ty
  where e2 : ty
  
  Cond(cond, e1, e2): rty
  where cond : Boolean()
   else error "Condition needs to be a Boolean()." on cond
    and e1 : t1
    and e2 : t2
    and (t1 <: t2 and t2 => rty)
     or (t2 <: t1 and t1 => rty)
  
  While(cond, expr): Void()
  where cond : Boolean()
   else error "Condition needs to be a Boolean()." on cond
  
  Throw(e): Void()
  where e : ClassRef(x)
   else error "Only classes may be thrown." on e
  
  Try(e1, cl, var, e2): ty
  where e1 : ty
    and e2 : ty'
    and ty == ty'
   else error "Types of the try and catch blocks are not compatible." on e1
  