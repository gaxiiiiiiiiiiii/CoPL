

Require Import ZArith.
Open Scope Z_scope.
Require Import ssreflect.


Inductive Value : Set :=
    | VInt : Z -> Value
    | VBool : bool -> Value.

Inductive Exp : Set :=
    | EValue : Value -> Exp
    | EIf    : Exp -> Exp -> Exp -> Exp 
    | EPlus  : Exp -> Exp -> Exp 
    | EMinus : Exp -> Exp -> Exp 
    | ETimes : Exp -> Exp -> Exp 
    | ELt    : Exp -> Exp -> Exp.


Inductive Plus : Z -> Z -> Z -> Prop :=
    | B_Plus : forall x y z, z = x + y -> Plus x y z.

Inductive Minus : Z -> Z -> Z -> Prop :=
    | B_Minus : forall x y z, z = x - y -> Minus x y z.

Inductive Times : Z -> Z -> Z -> Prop :=
    | B_Times : forall x y z, z = x * y -> Times x y z.
    
Inductive Lt : Z -> Z -> bool -> Prop :=
    | B_Lt : forall x y b, b = (x <? y) -> Lt x y b.
    
Theorem Plus_uniq :
    forall x y z1 z2, Plus x y z1 -> Plus x y z2 -> z1 = z2.
Proof.
    move => x y z1 z2 H1 H2.
    inversion H1; inversion H2; subst => //.
Qed. 

Theorem Minus_uniq :
    forall x y z1 z2, Minus x y z1 -> Minus x y z2 -> z1 = z2.
Proof.
    move => x y z1 z2 H1 H2.
    inversion H1; inversion H2; subst => //.
Qed. 

Theorem Times_uniq :
    forall x y z1 z2, Times x y z1 -> Times x y z2 -> z1 = z2.
Proof.
    move => x y z1 z2 H1 H2.
    inversion H1; inversion H2; subst => //.
Qed.   

Theorem Lt_uniq :
    forall x y b1 b2, Lt x y b1 -> Lt x y b2 -> b1 = b2.
Proof.
    move => x y b1 b2 H1 H2.
    inversion H1; inversion H2; subst => //.
Qed.

Inductive EvalTo : Exp -> Value -> Prop :=
    | E_Int   : forall i, EvalTo (EValue (VInt i)) (VInt i)
    | E_Bool  : forall b, EvalTo (EValue (VBool b)) (VBool b)
    | E_IfT   : forall B T F v, EvalTo B (VBool true)  -> EvalTo T v -> EvalTo (EIf B T F) v
    | E_IfF   : forall B T F v, EvalTo B (VBool false) -> EvalTo F v -> EvalTo (EIf B T F) v
    | E_Plus  : forall X Y x y z,
                EvalTo X (VInt x) -> EvalTo Y (VInt y) -> Plus x y z ->
                EvalTo (EPlus X Y) (VInt z)
    | E_Minus : forall X Y x y z,
                EvalTo X (VInt x) -> EvalTo Y (VInt y) -> Minus x y z ->
                EvalTo (EMinus X Y) (VInt z)
    | E_Times : forall X Y x y z,
                EvalTo X (VInt x) -> EvalTo Y (VInt y) -> Times x y z ->
                EvalTo (ETimes X Y) (VInt z)
    | E_Lt    : forall X Y x y b,
                EvalTo X (VInt x) -> EvalTo Y (VInt y) -> Lt x y b ->
                EvalTo (ELt X Y) (VBool b).

Lemma EvalTo_Bool : 
    forall E b, EvalTo E (VBool b) -> 
    (E = EValue (VBool b)) \/ 
    (exists B T F, E = EIf B T F )  \/
    (exists X Y, E = ELt X Y).
Proof.
    move => E b H.
    inversion H.
    +   left => //.
    +   right; left.
        exists B, T, F => //.
    +   right; left.
        exists B, T, F => //.
    +   right; right.
        exists X, Y => //.
Qed.

Lemma EvalTo_Int :
        forall E i, EvalTo E (VInt i) ->
        (E = EValue (VInt i)) \/ 
        (exists B T F, E = EIf B T F) \/ 
        (exists X Y, E = EPlus X Y) \/ 
        (exists X Y, E = EMinus X Y) \/ 
        (exists X Y, E = ETimes X Y).
Proof.
    move => E i H.
    inversion H.
    +   left => //.
    +   right; left.
        exists B, T, F => //.
    +   right; left.
        exists B, T, F => //.
    +   right; right; left.
        exists X, Y => //. 
    +   right; right; right; left.
        exists X, Y => //.
    +   right; right; right; right.
        exists X, Y => //.
Qed.          

Theorem EvalTo_uniq :
    forall E v1 v2, EvalTo E v1 -> EvalTo E v2 -> v1 = v2.
Proof.  
    elim.
    +   move => v v1 v2 H1 H2.
        inversion H1; inversion H2; subst => //.
    +   move => B HB T HT F HF v1 v2 H1 H2.
        inversion H1; inversion H2; subst.
        -   apply HT => //.
        -   move : (HB (VBool true) (VBool false) H5 H11) => f.
            inversion f.
        -   move : (HB (VBool true) (VBool false) H11 H5) => f.
            inversion f.
        -   apply HF => //.
    +   move => X HX Y HY v1 v2 H1 H2.
        inversion H1; inversion H2; subst.
        move : (HX (VInt x) (VInt x0) H3 H9) => Hx; inversion Hx.
        move : (HY (VInt y) (VInt y0) H4 H10) => Hy; inversion Hy.
        subst x0 y0.
        move : (Plus_uniq x y z z0 H6 H12) -> => //.
    +   move => X HX Y HY v1 v2 H1 H2.
        inversion H1; inversion H2; subst.
        move : (HX (VInt x) (VInt x0) H3 H9) => Hx; inversion Hx.
        move : (HY (VInt y) (VInt y0) H4 H10) => Hy; inversion Hy.
        subst x0 y0.
        move : (Minus_uniq x y z z0 H6 H12) -> => //.
    +   move => X HX Y HY v1 v2 H1 H2.
        inversion H1; inversion H2; subst.
        move : (HX (VInt x) (VInt x0) H3 H9) => Hx; inversion Hx.
        move : (HY (VInt y) (VInt y0) H4 H10) => Hy; inversion Hy.
        subst x0 y0.
        move : (Times_uniq x y z z0 H6 H12) -> => //.
    +   move => X HX Y HY v1 v2 H1 H2.
        inversion H1; inversion H2; subst.
        move : (HX (VInt x) (VInt x0) H3 H9) => Hx; inversion Hx.
        move : (HY (VInt y) (VInt y0) H4 H10) => Hy; inversion Hy.
        subst x0 y0.
        move : (Lt_uniq x y b b0 H6 H12) -> => //.
Qed.     


Inductive Error : Exp -> Prop :=
    | E_IfInt       : forall B T F i, EvalTo B (VInt i)  -> Error (EIf B T F)
    | E_PlusBoolL   : forall X Y b,   EvalTo X (VBool b) -> Error (EPlus X Y)
    | E_PlusBoolR   : forall X Y b,   EvalTo Y (VBool b) -> Error (EPlus X Y)
    | E_MinusBoolL  : forall X Y b,   EvalTo X (VBool b) -> Error (EMinus X Y)
    | E_MinusBoolR  : forall X Y b,   EvalTo Y (VBool b) -> Error (EMinus X Y)
    | E_TimesBoolL  : forall X Y b,   EvalTo X (VBool b) -> Error (ETimes X Y)
    | E_TimesBoolR  : forall X Y b,   EvalTo Y (VBool b) -> Error (ETimes X Y)
    | E_LtBoolL     : forall X Y b,   EvalTo X (VBool b) -> Error (ELt X Y)
    | E_LtBoolR     : forall X Y b,   EvalTo Y (VBool b) -> Error (ELt X Y)
    | E_IfTError    : forall B T F,   EvalTo B (VBool true)  -> Error T -> Error (EIf B T F)
    | E_IfFError    : forall B T F,   EvalTo B (VBool false) -> Error F -> Error (EIf B T F)
    | E_IfError     : forall B T F,   Error B -> Error (EIf B T F)
    | E_PlusErrorL  : forall X Y  ,   Error X -> Error (EPlus X Y)
    | E_PlusErrorR  : forall X Y  ,   Error Y -> Error (EPlus X Y)
    | E_MinusErrorL : forall X Y  ,   Error X -> Error (EMinus X Y)
    | E_MinusErrorR : forall X Y  ,   Error Y -> Error (EMinus X Y)
    | E_TimesErrorL : forall X Y  ,   Error X -> Error (ETimes X Y)
    | E_TimesErrorR : forall X Y  ,   Error Y -> Error (ETimes X Y)
    | E_LtErrorL    : forall X Y  ,   Error X -> Error (ELt X Y)
    | E_LtErrorR    : forall X Y  ,   Error Y -> Error (ELt X Y).

Theorem EvalTo_Error_total :
    forall e, (exists v, EvalTo e v) \/ Error e.
Proof.
    elim.
    +   move => v.
        left; exists v.
        induction v; [apply E_Int | apply E_Bool ].
    +   move => B HB T HT F HF.
        case HB as [[b Hb] | Eb]; last first.
        right; apply E_IfError => //.
        induction b as [i|b].
        right; apply E_IfInt with (i := i) => //.
        induction b.
        -   case HT as [[t Ht] | Et].
            *   left; exists t; apply E_IfT => //.
            *   right; apply E_IfTError => //.
        -   case HF as [[f Hf] | Ef].
            *   left; exists f; apply E_IfF => //.
            *   right; apply E_IfFError => //.
    +   move => X HX Y HY.
        case HX => [[x Hx]| Ex]; last first.
        right; apply E_PlusErrorL => //.
        induction x as [i|b]; last first.
        right; apply E_PlusBoolL with (b := b) => //.
        case HY => [[y Hy]| Ey]; last first.
        right; apply E_PlusErrorR => //.
        induction y as [j|b]; last first.
        right; apply E_PlusBoolR with (b := b) => //.
        left; exists (VInt (i + j)); apply (E_Plus _ _ i j) => //.
    +   move => X HX Y HY.
        case HX => [[x Hx]| Ex]; last first.
        right; apply E_MinusErrorL => //.
        induction x as [i|b]; last first.
        right; apply E_MinusBoolL with (b := b) => //.
        case HY => [[y Hy]| Ey]; last first.
        right; apply E_MinusErrorR => //.
        induction y as [j|b]; last first.
        right; apply E_MinusBoolR with (b := b) => //.
        left; exists (VInt (i - j)); apply (E_Minus _ _ i j) => //.
    +   move => X HX Y HY.
        case HX => [[x Hx]| Ex]; last first.
        right; apply E_TimesErrorL => //.
        induction x as [i|b]; last first.
        right; apply E_TimesBoolL with (b := b) => //.
        case HY => [[y Hy]| Ey]; last first.
        right; apply E_TimesErrorR => //.
        induction y as [j|b]; last first.
        right; apply E_TimesBoolR with (b := b) => //.
        left; exists (VInt (i * j)); apply (E_Times _ _ i j) => //.
    +   move => X HX Y HY.
        case HX => [[x Hx]| Ex]; last first.
        right; apply E_LtErrorL => //.
        induction x as [i|b]; last first.
        right; apply E_LtBoolL with (b := b) => //.
        case HY => [[y Hy]| Ey]; last first.
        right; apply E_LtErrorR => //.
        induction y as [j|b]; last first.
        right; apply E_LtBoolR with (b := b) => //.
        left; exists (VBool (i <? j)); apply (E_Lt _ _ i j) => //.
Qed.        








