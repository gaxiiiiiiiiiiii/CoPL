Inductive peano : Set :=
    | Z : peano
    | S : peano -> peano.


Inductive Plus : peano -> peano -> peano -> Prop :=
    | P_Zero : forall n, Plus Z n n
    | P_Succ : forall n m l,
                Plus n m l -> Plus (S n) m (S l).


Inductive Times : peano -> peano -> peano -> Prop :=
    | T_Zero : forall n, Times Z n Z
    | T_Succ : forall n m l o,
               Times n m l -> Plus m l o -> Times (S n) m o.

                
Inductive LessThan : peano -> peano -> Prop :=
    | L_Succ : forall n, LessThan n (S n)                
    | L_Trans : forall n m l,
                LessThan n m -> LessThan m l -> LessThan n l
    | L_Zero : forall n, LessThan Z (S n)
    | L_SuccSucc : forall n m ,
                   LessThan n m -> LessThan (S n) (S m)
    | L_SuccR : forall n m,
                LessThan n m -> LessThan n (S m).

Inductive Exp : Set :=
    | ENum : peano -> Exp
    | EPlus : Exp -> Exp -> Exp
    | ETimes : Exp -> Exp -> Exp.


Inductive EvalTo : Exp -> peano -> Prop :=
    | E_Const : forall n, EvalTo (ENum n) n
    | E_Plus : forall e1 e2 n1 n2 n,
               EvalTo e1 n1 -> EvalTo e2 n2 -> Plus n1 n2 n -> 
               EvalTo (EPlus e1 e2) n
    | E_Times : forall e1 e2 n1 n2 n,
                EvalTo e1 n1 -> EvalTo e2 n2 -> Times n1 n2 n -> 
                EvalTo (ETimes e1 e2) n.

Inductive ReduceTo : Exp -> Exp -> Prop :=
    | R_Plus : forall n m l,
               Plus n m l -> ReduceTo (EPlus (ENum n) (ENum m)) (ENum l)
    | R_Times : forall n m l,
                 Times n m l -> ReduceTo (ETimes (ENum n) (ENum m)) (ENum l)
    | R_PlusL : forall e1 e1' e2,
                ReduceTo e1 e1' -> ReduceTo (EPlus e1 e2) (EPlus e1' e2)
    | R_TimesL : forall e1 e1' e2,
                ReduceTo e1 e1' -> ReduceTo (ETimes e1 e2) (ETimes e1' e2)
    | R_PlusR : forall e1 e2 e2',
                ReduceTo e2 e2' -> ReduceTo (EPlus e1 e2) (EPlus e1 e2')
    | R_TimesR : forall e1 e2 e2',
                ReduceTo e2 e2' -> ReduceTo (ETimes e1 e2) (ETimes e1 e2').


Inductive MultiReduceTo : Exp -> Exp -> Prop :=
    | MR_Zero : forall e, MultiReduceTo e e
    | MR_One : forall e e', ReduceTo e e' -> MultiReduceTo e e'
    | MR_Multi : forall e e' e'',
                 MultiReduceTo e e' -> MultiReduceTo e' e'' ->
                 MultiReduceTo e e''.


Inductive DetReduceTo : Exp -> Exp -> Prop :=
    | DR_Plus : forall n m l,
                Plus n m l -> DetReduceTo (EPlus (ENum n) (ENum m)) (ENum l)
    | DR_Times : forall n m l,
                 Times n m l -> DetReduceTo (ETimes (ENum n) (ENum m)) (ENum l)
    | DR_PlusL  : forall e1 e1' e2 : Exp,
                DetReduceTo e1 e1' ->
                DetReduceTo (EPlus e1 e2) (EPlus e1' e2)
    | DR_PlusR  : forall (n1 : peano) (e2 e2' : Exp),
                DetReduceTo e2 e2' ->
                DetReduceTo (EPlus (ENum n1) e2) (EPlus (ENum n1) e2')
    | DR_TimesL : forall e1 e1' e2 : Exp,
                DetReduceTo e1 e1' ->
                DetReduceTo (ETimes e1 e2) (ETimes e1' e2)
    | DR_TimesR : forall (n1 : peano) (e2 e2' : Exp),
                DetReduceTo e2 e2' ->
                DetReduceTo (ETimes (ENum n1) e2) (ETimes (ENum n1) e2').     
                
Hint Constructors  Plus Times LessThan Exp EvalTo ReduceTo MultiReduceTo DetReduceTo : Peano.  

Export Peano.

Ltac autoP := auto with Peano.



               