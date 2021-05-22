

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

Theorem Times_assoc :
    forall x y z xy xyz,
    Times x y xy -> Times xy z xyz  ->
    exists yz, Times y z yz /\ Times x yz xyz.
Proof.
   






(* Theorem distr_l :
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
- suff Hl_ : Plus xy_ xz_ l.           *)




    
      
        











    
