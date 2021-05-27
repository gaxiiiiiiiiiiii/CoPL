

Require Import NaturalNumbers.
Require Export ssreflect.



Theorem Plus_unit_l :
    forall n, Plus Z n n.
Proof. autoP. Qed.


    Theorem Plus_unit_r n : Plus n Z n.
Proof.
    elim n => [|m IHm]; autoP.
Qed.

Theorem Plus_uniq :
    forall x y z1 z2, Plus x y z1 -> Plus x y z2 -> z1 = z2.
Proof.
    elim => [y z1 z2 H1 H2|x0 IH y z1 z2 H1 H2].
    + (* x == Z *)
      inversion H1.
      inversion H2.
      subst n n0 y => //.
    + (* x ==  (S x0)*)
      inversion H1.
      inversion H2.
      specialize (IH y l l0 H0 H6).
      rewrite IH => //.
Qed.


Theorem Plus_close :
    forall x y, exists z, Plus x y z.
Proof.
    move => x y.
    elim x => [|x0 IHx].

    + (* x == Z *)
      exists y; apply Plus_unit_l.

    + (* x == (S x0) *)
      induction IHx as [z H].
      exists (S z).
      apply P_Succ => //.
Qed.

Theorem P_Succ_r :
    forall x y z, Plus x y z -> Plus x (S y) (S z).
Proof.
    elim.
    
    + (* x == Z *)
      move => y z H.
      inversion H.
      apply Plus_unit_l.

    + (* x == (S x0) *)
      move => x0 IH y z H.
      inversion H.
      apply P_Succ.
      apply (IH y l) =>//.
Qed.


Theorem Plus_comm :
    forall x y z, Plus x y z -> Plus y x z.
Proof.
    elim => [|n IHn].            

    + (* x == Z *)
      move => y z H.
      inversion H.
      apply Plus_unit_r.
    
    + (* x == (S n) *)
      move => y z H.
      inversion H.
      apply P_Succ_r.
      apply IHn => //.
Qed.


Theorem Plus_assoc :
    forall x y z xy xyz,
    Plus x y xy -> Plus xy z xyz ->
    exists yz, Plus y z yz /\ Plus x yz xyz.
Proof.    
    elim => [| x0 IHx].

    + (* x == Z *)
      move => y z xy xyz Hl Hr.
      inversion Hl.
      inversion Hr.

      - subst n n0 xy.
        exists xyz.
        split; apply Plus_unit_l.

      - subst n xy.
        exists (S l).
        split.
        apply P_Succ=> //.
        apply Plus_unit_l.
   
    + (* x == (S x0)*)
      move => y z xy xyz Hl Hr.
      inversion Hl; move => {Hl}.
      subst n m xy.
      inversion Hr => {Hr}.
      subst n m xyz.
      specialize (IHx y z l l0 H0 H1).
      inversion IHx as [yz [Hl Hr]].
      exists yz; split => //.
      apply P_Succ => //.
Qed.


Theorem Times_uniq :
    forall x y z z', Times x y z -> Times x y z' -> z = z'.
Proof.
    elim => [|x0 IHx].
    + move => y z z' H1 H2.
      inversion H1; inversion H2  => //.
    + move => y z z' H1 H2.
      inversion H1; inversion H2 => {H1 H2}.
      subst n m o n0 m0 o0.
      suff ll : l = l0.
      - subst l0.
        apply (Plus_uniq y l) => //.
      - apply (IHx y l l0) => //.
Qed.          


Theorem Times_close :
    forall x y, exists z, Times x y z.
Proof.
    move => x y.
    elim  x=> [|x0 IHx].
    + exists Z; apply T_Zero.
    + inversion IHx as [z H]; move => {IHx}.
      induction (Plus_close y z) as [yz Hyz].
      exists yz.
      apply T_Succ with (l := z) => //.
Qed.

Theorem Times_zero_l :
    forall n, Times Z n Z.
Proof. autoP. Qed.
    

Theorem Times_zero_r :
    forall n, Times n Z Z.
Proof.
    elim => [|n0 IHn].
    + autoP.
    + apply T_Succ with (l := Z); autoP.
Qed.



Lemma T_Succ_r :
    forall n m l o,
    Times n m l -> Plus n l o -> Times n (S m) o.
Proof.
    move => n m.
    induction n,  m; move => l o H1 H2; inversion H1 => {H1}; inversion H2 => {H2}.
    + subst n l n0 o.
      apply T_Zero.
    + subst n l n0 o.
      apply T_Zero.
    + subst n0 m o0 n1 m0 o.
      apply T_Succ with (l := n).
      - apply IHn with (l := Z).
        apply Times_zero_r.
        apply Plus_unit_r.
      - apply P_Succ.
        inversion H3 => {H3}; subst n0 l0.
        suff nl : l1 = n.
        * subst l1.
          apply P_Zero.
        * suff lz : l = Z.
          subst l.
          apply (Plus_uniq n Z) => //.
          apply Plus_unit_r.
          apply (Times_uniq n Z) => //.
          apply Times_zero_r.
    + subst n0 m0 o0 n1 m1 o.
      inversion H3 => {H3}; subst n0 m0 l.
      specialize (Plus_close n l0); move => [z Hz].
      apply T_Succ with (l := z).
      - apply IHn with (l := l0) => //.
      - apply P_Succ.
        apply (Plus_comm n (S l2) l1) in H6.
        inversion H6 => {H6}; subst n0 m0 l1.
        specialize (Plus_assoc m l0 n l2 l H1 H2).
        move => [z_ [H3 H4]].
        apply P_Succ.
        suff zz : z = z_.
        * subst z_ => //.
        * apply (Plus_uniq n l0) => //.
          apply Plus_comm => //.
Qed.






Theorem Times_comm :
    forall x y z, Times x y z -> Times y x z.
Proof.
    elim => [| x0 IHx].
    + move => y z H; inversion H; subst n z.
      apply Times_zero_r.
    + move => y z H; inversion H; subst n m o.
      apply T_Succ_r with (l := l) => //.
      apply IHx => //.
Qed. 

Theorem Times_eq_Z :
    forall x y, Times x y Z -> x = Z \/ y = Z.
Proof.
    move => x y.
    induction x, y => H.
    + left => //.
    + left => //.
    + right => //.
    + inversion H; subst n m o.
      inversion H2.
Qed.   

Lemma dist_l :
    forall x y z yz xyxz , Times x yz xyxz -> Plus y z yz ->
    exists xy xz, Times x y xy /\ Times x z xz /\ Plus xy xz xyxz.
Proof.    
    elim => [|x_ IHx] => y z yz xyxz HT HP.
    + inversion HT; subst n xyxz.
      exists Z, Z; autoP.
    + inversion HT; subst n m o.
      move : (IHx y z yz l H0 HP) => [xy_ [xz_ [Hxy_ [Hxz_ Hl]]]].
      move : (Plus_close y xy_) => [xy Hxy].
      move : (Plus_close z xz_) => [xz Hxz].
      exists xy, xz; split; [|split].
      - apply T_Succ with (l := xy_) => //.
      - apply T_Succ with (l := xz_) => //.
      - move : (Plus_assoc y z l yz xyxz HP H1) => [zl [Hzl Hyzl]].
        apply Plus_comm in Hzl.
        move  : (Plus_assoc xy_ xz_ z l zl Hl Hzl) => [xz' [Hxz' Hzl']].
        apply Plus_comm in Hxz; apply Plus_comm in Hxy.
        move : (Plus_uniq xz_ z xz xz' Hxz Hxz') => xzxz; subst xz'.
        apply Plus_comm in Hzl'.
        apply Plus_comm in Hyzl.
        move : (Plus_assoc xz xy_ y zl xyxz Hzl' Hyzl) => [xy' [Hxy' Hyz']].
        move : (Plus_uniq xy_ y xy xy' Hxy Hxy') => xyxy; subst xy'.
        apply Plus_comm => //.
Qed.        

Lemma dist_r :
    forall x y z xy xzyz, Times xy z xzyz -> Plus x y xy ->
    exists xz yz, Times x z xz /\ Times y z yz /\ Plus xz yz xzyz.
Proof.
    move => x y z xy xzyz HT HP.
    apply Times_comm in HT.
    move : (dist_l z x y xy xzyz HT HP) => [xz [yz [Hxz [Hyz H]]]].
    exists xz, yz; split; [|split] => //; apply Times_comm => //.
Qed.



    
           

Theorem Times_assoc :
    forall x y z xy xyz,
    Times x y xy -> Times xy z xyz  ->
    exists yz, Times y z yz /\ Times x yz xyz.
Proof.
    move => x y; move : x.
    induction y => x z xy xyz H1 H2.
    + apply Times_comm in H1.
      inversion H1; subst n xy.
      inversion H2; subst n xyz.
      exists Z; split => //.
      apply Times_zero_r.
    + apply Times_comm in H1.
      inversion H1; subst n m o.
      move : (Times_close y z) => [yz_ Hyz_].
      move : (Plus_close z yz_) => [yz Hyz].
      exists yz; split.
      - apply T_Succ with (l := yz_) => //.
      - move : (dist_r x l z xy xyz H2 H3) => [xz [lz [Hzx [Hlz Hxyz]]]]. 
        move : (Times_close x yz) => [xyz' H].
        move :  (dist_l x z yz_ _ _ H Hyz) => [xz' [yz' [Hxz [Hxyz_ Hxyz']]]].
        move : (Times_uniq x z _ _ Hzx Hxz) => xzxz; subst xz'.
        apply Times_comm in H0.
        move : (IHy x z l lz H0 Hlz) => [yz'' [Hyz'' Hlz']].
        move : (Times_uniq y z _ _ Hyz_ Hyz'') => yzyz; subst yz''.
        suff : xyz = xyz'.
          move => -> //.
        apply (Plus_uniq xz lz) => //.
        suff  : lz = yz'.
          move => -> //.
        apply (Times_uniq x yz_) => //.
Qed.



(* Theorem 2.11 (CompareNat1) *)
Theorem LessThan1_Z_Sn :
    forall n : peano, LessThan1 Z (S n).
Proof.
    induction n as [| n' H'].
    
        (* Case : n = Z *)
        apply L1_Succ.
    
        (* Case : n = S n' *)
        apply (L1_Trans _ (S n') _ H').
        apply L1_Succ.
Qed.

(* Theorem 2.11 (CompareNat2) *)
Theorem LessThan2_Z_Sn :
    forall n : peano, LessThan2 Z (S n).
Proof.
    apply L2_Zero.
Qed.

(* Theorem 2.11 (CompareNat3) *)
Theorem LessThan3_Z_Sn :
    forall n : peano, LessThan3 Z (S n).
Proof.
    induction n as [| n' H].
    
        (* Case : n = Z *)
        apply L3_Succ.
    
        (* Case : n = S n' *)
        apply (L3_SuccR _ _ H).
Qed.

(* Theorem 2.12 (CompareNat1) *)
Theorem LessThan1_prev :
    forall n1 n2 : peano, LessThan1 (S n1) (S n2) -> LessThan1 n1 n2.
Proof.
Admitted.

(* Theorem 2.12 (CompareNat2) *)
Theorem LessThan2_prev :
    forall n1 n2 : peano, LessThan2 (S n1) (S n2) -> LessThan2 n1 n2.
Proof.
Admitted.

(* Theorem 2.12 (CompareNat3) *)
Theorem LessThan3_prev :
    forall n1 n2 : peano, LessThan3 (S n1) (S n2) -> LessThan3 n1 n2.
Proof.
Admitted.

(* Theorem 2.13 (CompareNat1) *)
Theorem LessThan1_trans :
    forall n1 n2 n3 : peano,
    LessThan1 n1 n2 -> LessThan1 n2 n3 -> LessThan1 n1 n3.
Proof.
    apply L1_Trans.
Qed.

(* Theorem 2.13 (CompareNat2) *)
Theorem LessThan2_trans :
    forall n1 n2 n3 : peano,
    LessThan2 n1 n2 -> LessThan2 n2 n3 -> LessThan2 n1 n3.
Proof.
Admitted.

(* Theorem 2.13 (CompareNat3) *)
Theorem LessThan3_trans :
    forall n1 n2 n3 : peano,
    LessThan3 n1 n2 -> LessThan3 n2 n3 -> LessThan3 n1 n3.
Proof.
Admitted.

(* Theorem 2.14 (1) (2) *)
Theorem LessThan_equiv_1_2 :
    forall n1 n2 : peano, LessThan1 n1 n2 <-> LessThan2 n1 n2.
Proof.
Admitted.

(* Theorem 2.14 (2) (3) *)
Theorem LessThan_equiv_2_3 :
    forall n1 n2 : peano, LessThan2 n1 n2 <-> LessThan3 n1 n2.
Proof.
Admitted.

(* Theorem 2.14 (1) (3) *)
Theorem LessThan_equiv_1_3 :
    forall n1 n2 : peano, LessThan1 n1 n2 <-> LessThan3 n1 n2.
Proof.
Admitted.

Theorem EvalTo_total :
    forall e, exists n, EvalTo e n.
Proof.
    move => e.
    (* inversion e as [n| x y | x y]. *)
    induction e as [n | x [x_ Hx] y [y_ Hy]| x [x_ Hx] y [y_ Hy]].
    +   exists n.
        apply E_Const.
    +   move : (Plus_close x_ y_) => [xy Hxy].
        exists xy.
        apply (E_Plus x y x_ y_ xy) => //.
    +   move : (Times_close x_ y_) => [xy Hxy].
        exists xy.
        apply (E_Times x y x_ y_ xy) => //.
Qed.  

Theorem EvalTo_uniq :
    forall e x y, EvalTo e x -> EvalTo e y -> x = y.
Proof.
    elim => [|e_ He_|e_ He_].
    +   move => p x y H1 H2.
        inversion H1; inversion H2.
        subst n n0 p => //.
    +   move => e He x y H1 H2.
        inversion H1; inversion H2.
        subst e1 e2 n e0 e3 n4.
        suff H : n1 = n0 /\ n2 = n3.
        -   inversion H.
            subst n0 n3.
            apply (Plus_uniq n1 n2) => //.
        -   split.
            *   apply He_ => //.
            *   apply He => //.
    +   move => e He x y H1 H2.
        inversion H1; inversion H2.
        subst e1 e2 n e0 e3 n4.
        suff H : n1 = n0 /\ n2 = n3.
        -   inversion H.
            subst n0 n3.
            apply (Times_uniq n1 n2) => //.
        -   split.
            *   apply He_ => //.
            *   apply He => //.
Qed.      

Theorem EPlus_comm : 
    forall X Y xy, EvalTo (EPlus X Y) xy -> EvalTo (EPlus Y X) xy.
Proof.
    move => X Y xy H.
    inversion H.
    apply (E_Plus Y X n2 n1) => //.
    apply Plus_comm => //.
Qed.

Theorem EPlus_assoc :
    forall X Y Z xyz,
    EvalTo (EPlus (EPlus X Y) Z) xyz -> EvalTo (EPlus X (EPlus Y Z)) xyz.
Proof.
    move => X Y Z xyz H.
    inversion H.
    inversion H2.
    subst e1 e2 n e0 e3 n4.
    move : (Plus_close n3 n2) => [yz Hyz].
    apply (E_Plus _ _ n0 yz) => //.
    +   apply (E_Plus Y Z n3 n2) => //.
    +   move :  (Plus_assoc n0 n3 n2 n1 xyz H11 H5) => [yz_ [Hyz_ Hxyz]].
        suff : yz = yz_.
        -   move => -> //.
        -   apply (Plus_uniq n3 n2) => //.
Qed.

Theorem ETimes_comm :
    forall X Y n, EvalTo (ETimes X Y) n -> EvalTo (ETimes Y X) n.
Proof.
    move => X Y n H.
    inversion H.
    apply (E_Times Y X n2 n1) => //.
    apply Times_comm => //. 
Qed.


Theorem ETimes_assoc :
    forall X Y Z xyz,
    EvalTo (ETimes (ETimes X Y) Z) xyz -> EvalTo (ETimes X (ETimes Y Z)) xyz.
Proof.
    move => X Y Z xyz H.
    inversion H.
    inversion H2.
    subst e1 e2 n e0 e3 n4.
    move : (Times_close n3 n2) => [yz Hyz].
    apply (E_Times _ _ n0 yz) => //.
    +   apply (E_Times Y Z n3 n2) => //.
    +   move :  (Times_assoc n0 n3 n2 n1 xyz H11 H5) => [yz_ [Hyz_ Hxyz]].
        suff : yz = yz_.
        -   move => -> //.
        -   apply (Times_uniq n3 n2) => //.
Qed.

Theorem ReduceTo_progress :
    forall e, (exists n, e = ENum n) \/ (exists e', ReduceTo e e').
Proof.
    move => e.
    induction e.
    +   left; exists p => //.
    +   move : IHe1 => [[x Hx]|[X HX]]; move : IHe2 => [[y Hy] | [Y HY]].
        -   subst e1 e2.
            move : (Plus_close x y) => [xy Hxy].
            right; exists (ENum xy).
            apply (R_Plus x y xy) => //.
        -   subst e1.
            right.
            exists (EPlus (ENum x) Y).
            apply R_PlusR => //.
        -   subst e2; right.
            exists (EPlus X (ENum y)).
            apply R_PlusL => //.
        -   right.
            exists (EPlus e1 Y).
            apply R_PlusR => //.
    +   move : IHe1 => [[x Hx]|[X HX]]; move : IHe2 => [[y Hy] | [Y HY]].
        -   subst e1 e2.
            move : (Times_close x y) => [xy Hxy].
            right; exists (ENum xy).
            apply (R_Times x y xy) => //.
        -   subst e1.
            right.
            exists (ETimes (ENum x) Y).
            apply R_TimesR => //.
        -   subst e2; right.
            exists (ETimes X (ENum y)).
            apply R_TimesL => //.
        -   right.
            exists (ETimes e1 Y).
            apply R_TimesR => //.
Qed.







Theorem DetReduceTo_uniq :
    forall X Y1 Y2, DetReduceTo X Y1 -> DetReduceTo X Y2 -> Y1 = Y2.
Proof.
    move => X; induction X => Y1 Y2 H1 H2.        
    +   inversion H1.
    +   inversion H1; subst X1 X2 Y1; inversion H2.
        *   subst n0 m0 Y2.
            move : (Plus_uniq n m l l0 H4 H5) -> => //.
        *   subst e1 e2 Y2.
            inversion H5.
        *   subst n1 e2 Y2.
            inversion H5.
        *   subst e1 e2 Y2.
            inversion H4.
        *   subst e0 e3 Y2.
            suff : e1' = e1'0.
            -   move => -> //.
            -   apply IHX1 => //.
        *   subst e1 e2 Y2.
            inversion H4.
        *   subst n1 e2 Y2.
            inversion H4.
        *   subst e1 e0 Y2.
            inversion H5.
        *   subst n0 e0 Y2.
            move : (IHX2 e2' e2'0 H4 H5) -> => //.
    +   inversion H1; subst X1 X2 Y1; inversion H2.
        *   subst n0 m0 Y2.
            move : (Times_uniq n m l l0 H4 H5) -> => //.
        *   subst e1 e2 Y2.
            inversion H5.
        *   subst n1 e2 Y2.
            inversion H5.
        *   subst e1 e2 Y2.
            inversion H4.
        *   subst e0 e3 Y2.
            suff : e1' = e1'0.
            -   move => -> //.
            -   apply IHX1 => //.
        *   subst e1 e2 Y2.
            inversion H4.
        *   subst n1 e2 Y2.
            inversion H4.
        *   subst e1 e0 Y2.
            inversion H5.
        *   subst n0 e0 Y2.
            move : (IHX2 e2' e2'0 H4 H5) -> => //.
Qed.   


    
Theorem DetReduceTo_ReduceTo :
    forall X Y, DetReduceTo X Y -> ReduceTo X Y.
Proof.
    elim.
    +   move => x Y H.
        inversion H.
    +   move => a IHa b IHb Y H.
        inversion H.
        *   subst a b Y.
            apply R_Plus => //.
        *   subst e1 e2 Y.
            apply R_PlusL.
            apply IHa => //.
        *   subst a b Y.
            apply R_PlusR.
            apply IHb => //.
    +   move => a IHa b IHb Y H.
        inversion H.
        *   subst a b Y.
            apply R_Times => //.
        *   subst e1 e2 Y.
            apply R_TimesL.
            apply IHa => //.
        *   subst a b Y.
            apply R_TimesR.
            apply IHb => //.
Qed.  

Lemma MR_PlusR :
    forall X Y Y', MultiReduceTo Y Y' -> 
    MultiReduceTo (EPlus X Y) (EPlus X Y').
Proof.
    move => X Y Y' H.
    elim H.
    +   move => e.
        apply MR_Zero.
    +   move => e e' He.
        apply MR_One.
        apply R_PlusR => //.
    +   move => x y z Hxy IHxy Hyz IHyz.
        apply (MR_Multi _ _ _ IHxy IHyz).
Qed.  

Lemma MR_PlusL :
    forall X X' Y, MultiReduceTo X X' ->
    MultiReduceTo (EPlus X Y) (EPlus X' Y).
Proof.
    move => X Y Y' H.
    elim H.
    +   move => e.
        apply MR_Zero.
    +   move => e e' He.
        apply MR_One.
        apply R_PlusL => //.
    +   move => x y z Hxy IHxy Hyz IHyz.
        apply (MR_Multi _ _ _ IHxy IHyz).
Qed.  

Lemma MR_TimesR :
    forall X Y Y', MultiReduceTo Y Y' -> 
    MultiReduceTo (ETimes X Y) (ETimes X Y').
Proof.
    move => X Y Y' H.
    elim H.
    +   move => e.
        apply MR_Zero.
    +   move => e e' He.
        apply MR_One.
        apply R_TimesR => //.
    +   move => x y z Hxy IHxy Hyz IHyz.
        apply (MR_Multi _ _ _ IHxy IHyz).
Qed.  

Lemma MR_TimesL :
    forall X X' Y, MultiReduceTo X X' ->
    MultiReduceTo (ETimes X Y) (ETimes X' Y).
Proof.
    move => X Y Y' H.
    elim H.
    +   move => e.
        apply MR_Zero.
    +   move => e e' He.
        apply MR_One.
        apply R_TimesL => //.
    +   move => x y z Hxy IHxy Hyz IHyz.
        apply (MR_Multi _ _ _ IHxy IHyz).
Qed.  



Theorem ReduceTo_weak_normal :
    forall e, exists n, MultiReduceTo e (ENum n).
Proof.
    elim.
    +   move => x; exists x.
        apply MR_Zero.
    +   move => X [x Hx] Y [y Hy].
        move : (Plus_close x y) => [xy Hxy].        
        exists xy.
        refine (MR_Multi _ (EPlus X (ENum y)) _ _ _).
        -   apply MR_PlusR => //.
        -   refine (MR_Multi _ (EPlus (ENum x) (ENum y)) _ _ _ ).
            *   apply MR_PlusL => //.
            *   apply MR_One.
                apply R_Plus => //.
    +   move => X [x Hx] Y [y Hy].
        move : (Times_close x y) => [xy Hxy].        
        exists xy.
        refine (MR_Multi _ (ETimes X (ENum y)) _ _ _).
        -   apply MR_TimesR => //.
        -   refine (MR_Multi _ (ETimes (ENum x) (ENum y)) _ _ _ ).
            *   apply MR_TimesL => //.
            *   apply MR_One.
                apply R_Times => //.
Qed.  

Theorem ReduceTo_confl :
   forall X Y1 Y2, ReduceTo X Y1 -> ReduceTo X Y2 ->
    exists Z, MultiReduceTo Y1 Z /\ MultiReduceTo Y2 Z.
Proof.
    elim.
    +   move => x Y1 Y2 H1.
        inversion H1.
    +   move => A HA B HB Y1 Y2 H1 H2.
        inversion H1; inversion H2.
        -   subst A B Y1 Y2.
            inversion H5; inversion H7.
            subst n0 m0.
            move : (Plus_uniq n m l l0 H4 H8) ->.
            exists (ENum l0); split; apply MR_Zero.
        -   subst A B Y1 Y2 e1 e2.
            inversion H8.
        -   subst A B e1 e2 Y1 Y2.
            inversion H8.
        -   subst A B e1 e2 Y1 Y2.
            inversion H4.
        -   subst A B e0 e3 Y1 Y2.
            move : (HA e1' e1'0 H4 H8) => [Z [HZ1 HZ2]].
            exists (EPlus Z e2); split; apply MR_PlusL => //.
        -   subst A B e0 e3 Y1 Y2.
            exists (EPlus e1' e2'); split.
            *   apply MR_PlusR; apply MR_One => //.
            *   apply MR_PlusL; apply MR_One => //.
        -   subst A B e1 e2 Y1 Y2.
            inversion H4.
        -   subst A B e0 e3 Y1 Y2. 
            exists (EPlus e1' e2'); split.
            *   apply MR_PlusL; apply MR_One => //.
            *   apply MR_PlusR; apply MR_One => //.
        -   subst A B e0 e3 Y1 Y2.
            move : (HB e2' e2'0 H4 H8) => [z [Hz1 Hz2]].
            exists (EPlus e1 z); split; apply MR_PlusR => //.
    +   move => A HA B HB Y1 Y2 H1 H2.
        inversion H1; inversion H2.
        -   subst A B Y1 Y2.
            inversion H5; inversion H7.
            subst n0 m0.
            move : (Times_uniq n m l l0 H4 H8) ->.
            exists (ENum l0); split; apply MR_Zero.
        -   subst A B Y1 Y2 e1 e2.
            inversion H8.
        -   subst A B e1 e2 Y1 Y2.
            inversion H8.
        -   subst A B e1 e2 Y1 Y2.
            inversion H4.
        -   subst A B e0 e3 Y1 Y2.
            move : (HA e1' e1'0 H4 H8) => [Z [HZ1 HZ2]].
            exists (ETimes Z e2); split; apply MR_TimesL => //.
        -   subst A B e0 e3 Y1 Y2.
            exists (ETimes e1' e2'); split.
            *   apply MR_TimesR; apply MR_One => //.
            *   apply MR_TimesL; apply MR_One => //.
        -   subst A B e1 e2 Y1 Y2.
            inversion H4.
        -   subst A B e0 e3 Y1 Y2. 
            exists (ETimes e1' e2'); split.
            *   apply MR_TimesL; apply MR_One => //.
            *   apply MR_TimesR; apply MR_One => //.
        -   subst A B e0 e3 Y1 Y2.
            move : (HB e2' e2'0 H4 H8) => [z [Hz1 Hz2]].
            exists (ETimes e1 z); split; apply MR_TimesR => //.
Qed.            
                    



Theorem EvalTo_MultiReduceTo :
    forall e n, EvalTo e n -> MultiReduceTo e (ENum n).
Proof.
    elim.
    +   move => m n H.
        inversion H.
        subst n0 m.
        apply MR_Zero.        
    +   move => x Hx y Hy n H.
        inversion H.
        subst e1 e2 n0.
        move : (Hx n1 H2) => H1 {H2 Hx}.
        move : (Hy n2 H3) => H2 {H3 Hy}.
        refine (MR_Multi _ (EPlus x (ENum n2))_ _ _).
        *   apply MR_PlusR => //.
        *   refine (MR_Multi _ (EPlus (ENum n1) (ENum n2))_ _ _).
            -   apply MR_PlusL => //.
            -   apply MR_One.
                apply R_Plus => //.
    +   move => x Hx y Hy n H.
        inversion H.
        subst e1 e2 n0.
        move : (Hx n1 H2) => H1 {H2 Hx}.
        move : (Hy n2 H3) => H2 {H3 Hy}.
        refine (MR_Multi _ (ETimes x (ENum n2))_ _ _).
        *   apply MR_TimesR => //.
        *   refine (MR_Multi _ (ETimes (ENum n1) (ENum n2))_ _ _).
            -   apply MR_TimesL => //.
            -   apply MR_One.
                apply R_Times => //.
Qed.




Lemma MR_eq :
    forall x y, MultiReduceTo (ENum x) (ENum y) -> x = y.
Proof.
    move => x y H.
    inversion H => //.
    +   inversion H0.
    +   subst e e''.
        (* move : (ReduceTo_weak_normal e') => [z Hz]. *)
        inversion H0; inversion H1.
        -   subst e e' e0.
            inversion H5 => //.
        -   subst e e' e0 e'0.
            inversion H4.
        -   subst e e' e0 e''.
Admitted.            





Theorem MultiReduceTo_EvalTo :
    forall e n, MultiReduceTo e (ENum n) -> EvalTo e n.
Proof.
Admitted.



    









    
    





    



      
    

    



           

        
       
          

    
        

       
         



