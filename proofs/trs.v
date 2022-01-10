Module AST.

Require Import FunInd.
From Coq Require Import Arith Bool Ascii String ZArith.Int.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import Coq.Program.Wf.
Require Import Coq.Arith.Plus.

Inductive sigma : Type := a | b. 

Inductive contEff : Type :=
| bot
| emp
| wildcard
| stop
| singleton (s: sigma)
| not       (s: sigma)
| cons      (es1: contEff) (es2: contEff)
| disj      (es1: contEff) (es2: contEff)
| kleene    (es: contEff).


Definition hypothesis : Type := list (contEff * contEff).

(*returns a set of hypothesis and the entailment validility*)
Definition result : Type := (hypothesis * bool).

Fixpoint leftHy' (n:nat) (records : hypothesis) : nat :=
match records with 
  | nil => n
  | x::xs => (leftHy' (n-1) xs)
end.

Definition compareEvent (s1 s2: sigma): bool :=
match (s1, s2) with 
| (a, a) => true 
| (b, b) => true 
| _ => false 
end.


Fixpoint compareEff (eff1 eff2: contEff): bool :=
match eff1, eff2 with
| bot, bot => true
| emp, emp => true
| stop, stop => true
| wildcard, wildcard => true
| singleton s1, singleton s2 => if compareEvent s1 s2 then true else false
| not s1, not s2 => if compareEvent s1 s2 then true else false
| cons e1 e2, cons e3 e4 => compareEff e1 e3 && compareEff e2 e4
| disj e1 e2, disj e3 e4 => (compareEff e1 e3 && compareEff e2 e4) ||
                            (compareEff e1 e4 && compareEff e2 e3)
| kleene e1, kleene e2 => compareEff e1 e2
| _,_ => false
end.


Fixpoint normal (eff:contEff) :contEff :=
match eff with
   | cons bot  _  => bot
   | cons _ bot   => bot
   | cons stop _  => emp
   | cons emp e   => normal e
   | cons e emp   => normal e
   | cons e1 e2   =>  
    (
      match normal e1, normal e2 with 
      | emp, e   => e
      | e, emp   => e
      | bot, _   => bot
      | _, bot   => bot
      | stop, e  => emp 
      | _, _ => (cons (normal e1) (normal e2))
      end
    )
    
   | disj bot e   => normal e
   | disj e bot   => normal e
   | disj e1 e2   =>  
    (
      match normal e1, normal e2 with 
      | bot, e  => e
      | e, bot  => e
      | stop, e  =>  disj emp e
      | _, _ => (disj (normal e1) (normal e2))
      end
    )
   
   | kleene emp   => emp
   | kleene e     =>  
    (match normal e with 
    | emp => emp
    | _   =>(kleene (normal e))
    end)
   | _ => eff
end.

Fixpoint reoccurTRS (hy:hypothesis) (lhs rhs: contEff) : bool :=
match hy with
| [] => false
| (lhs', rhs')::xs => if compareEff (normal lhs) (normal lhs') &&  compareEff (normal rhs) (normal rhs') then true else reoccurTRS xs lhs rhs
end.

Fixpoint nullable (eff:contEff): bool :=
match eff with
| bot          => false
| emp          => true
| singleton _  => false
| not   _      => false 
| stop         => true
| wildcard     => false
| disj e1 e2   => nullable e1 || nullable e2
| cons e1 e2   => nullable e1 && nullable e2
| kleene _     => true
end.

Inductive fstT : Type := one (s:sigma) | zero (s:sigma) | any.

Fixpoint fst (eff:contEff): list fstT  :=
match eff with
| bot          => []
| emp          => []
| singleton i  => [(one i)]
| wildcard     => [any]
| stop         => []
| not i        => [(zero i)] 
| disj e1 e2   => fst e1 ++ fst e2
| cons e1 e2   => if nullable e1 then fst e1 ++ fst e2
                  else fst e1
| kleene e     => fst e
end.

Definition entailFst (f1 f2 : fstT) : bool :=
  match f1, f2 with 
  | one s1, one s2 => compareEvent s1 s2 
  | zero s1, zero s2 => compareEvent s1 s2 
  | _, any => true
  | _, _ => false 
  end.


Fixpoint derivitive (eff:contEff) (f:fstT) : contEff :=
match eff with
| bot          => bot
| emp          => bot
| singleton i  => match entailFst f (one i)  with
                  | true => emp 
                  | flase => bot
end
| not   i      => match entailFst f (zero i) with
                  | true => emp 
                  | false =>bot
end 
| wildcard     => emp 
| stop         => bot
| cons e1 e2   => match nullable e1 with
                  | true => disj (cons (derivitive e1 f) e2)  (derivitive e2 f)
                  | flase => cons (derivitive e1 f) e2
end
| disj e1 e2   => disj (derivitive e1 f) (derivitive e2 f)
| kleene e     => cons (derivitive e f) eff
end.



Definition neg (v:bool): bool :=
match v with
| true => false
| false => true
end.


Local Open Scope nat_scope.

Fixpoint entailment (n:nat) (hy:hypothesis) (lhs rhs: contEff): bool :=
  match n with 
  | O => true  
  | S n' =>
    (
      match nullable lhs, nullable rhs with 
      | true , false => false 
      | _, _ =>  
        (
          match reoccurTRS hy lhs rhs with 
          | true => true 
          | false => 
    let fst := fst lhs in
    let subTrees := List.map (fun f =>
        let der1 := (derivitive lhs f) in
        let der2 := (derivitive rhs f) in
        entailment (n') ((lhs, rhs) :: hy) der1 der2
        ) fst in
    List.fold_left (fun acc a => acc && a) subTrees true
          end
        )
      end
    )
  end.

Definition entailmentShell (n:nat) (lhs rhs: contEff) : bool :=
  entailment n [] lhs rhs.


(*
Lemma nothing_entails_bot:
  forall (rhs: contEff),
    compareEff (normal rhs) bot = false -> 
    exists n, entailment n [] rhs bot = false.
Proof.
  intro.
  induction rhs.
  - unfold compareEff.  intro. discriminate H.
  - exists 1. unfold compareEff. unfold entailment.
    unfold nullable.  reflexivity.
  - exists 2. unfold compareEff. unfold entailment.
    unfold nullable. fold nullable. unfold reoccurTRS. 
    unfold fst. fold fst. 
    unfold map. unfold map. 
    unfold derivitive. unfold fst. 
    unfold fold_left.
    rewrite andb_true_l. unfold nullable. reflexivity.
  - unfold compareEff. intro H. exists 1.
    unfold entailment. unfold nullable. reflexivity.
  - unfold compareEff. intro. exists 2.
    unfold entailment. unfold nullable. unfold reoccurTRS.
    unfold fst. fold fst. 
    unfold map. unfold map. 
    unfold derivitive. unfold entailFst.
    case_eq  (compareEvent s s).
    + intros. unfold fold_left. rewrite andb_true_l. reflexivity.
    + unfold compareEvent.
      induction s.
      * intro. discriminate H0.
      * intro. discriminate H0.
  - unfold compareEff. intro. exists 2.
    unfold entailment. unfold nullable. unfold reoccurTRS.
    unfold fst. fold fst. 
    unfold map. unfold map. 
    unfold derivitive. unfold entailFst.
    case_eq  (compareEvent s s).
    + intros. unfold fold_left. rewrite andb_true_l. reflexivity.
    + unfold compareEvent.
      induction s.
      * intro. discriminate H0.
      * intro. discriminate H0.
  - 
    induction rhs1. 
    induction rhs2.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + unfold normal. unfold compareEff. intros. discriminate H.
    + intros. exists 3. unfold entailment. unfold nullable. fold nullable.
      rewrite andb_true_l.  unfold derivitive. fold derivitive.
      unfold nullable. fold nullable. unfold reoccurTRS.
      rewrite andb_false_l. 
      case_eq (nullable rhs2).
      * intros. reflexivity. 
      * intros. unfold normal. fold normal. fold fold_left. 
        unfold fst. fold fst. unfold nullable. fold nullable. 
        Search ([] ++ _ ). unfold map. fold map. unfold fold_left. 
        fold fold_left.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + 
  *)

Lemma bot_entails_everything:
  forall (rhs: contEff) , 
    entailment 1 [] bot rhs = true.
Proof.
  intro rhs.
  intros. unfold entailment. fold entailment.
  unfold nullable. unfold reoccurTRS. unfold derivitive. unfold normal.
  unfold fst. unfold map. unfold fold_left. reflexivity.
Qed.

Lemma emp_entails_nullable:
  forall (rhs: contEff) (hy:hypothesis), 
    nullable rhs = true ->
    entailment 1 [] emp rhs = true.
Proof. 
  intro rhs.
  intro. intro.
  unfold entailment. fold entailment. unfold nullable. fold nullable.
  destruct (nullable rhs) as [].
  - unfold reoccurTRS. unfold derivitive. unfold normal.
    unfold fst. unfold map. unfold fold_left. reflexivity.
  - discriminate H.
Qed.

Lemma nullable_wildcard_any_imply_wildcard_one:
  forall (eff: contEff) (s:sigma) (f:fstT), 
    nullable (derivitive eff any) = true ->
    nullable (derivitive eff f) = true.
Proof. 
  intro eff. induction eff.
  - intro s. intro f.
    unfold derivitive. unfold normal. unfold nullable. intro H. discriminate H.
  - intro s. intro f.
    unfold derivitive. unfold normal. unfold nullable. intro H. discriminate H.
  - intro s. intro f.
    unfold derivitive. unfold normal. unfold nullable. intro H. reflexivity. 
  - intro s. intro f.
    unfold derivitive. unfold normal. unfold nullable. intro H.  discriminate H.
  - intro s'. intro f.
    unfold derivitive. unfold entailFst. unfold normal. fold normal. unfold nullable.
    intro H.  discriminate H.
  - intro s'. intro f.
    unfold derivitive. unfold entailFst. unfold normal. fold normal. unfold nullable.
    intro H.  discriminate H.
  - intro s'. unfold derivitive. fold derivitive. 
    intro f. 
    case_eq (nullable eff1). 
    + unfold nullable. fold nullable. intros. 
      assert (temp := orb_prop (nullable (derivitive eff1 any) && nullable eff2) (nullable (derivitive eff2 any)) H0).
      intros. Search (_ || _ = true). 
      destruct temp.
      *  intros. Search (_ &&  _ = true -> _ ).  
         destruct (andb_prop (nullable (derivitive eff1 any)) (nullable eff2) H1).
         rewrite  (orb_true_iff (nullable (derivitive eff1 f) && nullable eff2 ) (nullable (derivitive eff2 f))).
         left. rewrite (IHeff1 s' f ). 
         -- rewrite  (andb_true_iff true (nullable eff2)). split. reflexivity. exact H3.
         -- exact H2.
      *  rewrite  (orb_true_iff (nullable (derivitive eff1 f) && nullable eff2 ) (nullable (derivitive eff2 f))).
         right.
         exact (IHeff2 s' f H1).
    + unfold nullable. fold nullable. intros. 
      destruct (andb_prop (nullable (derivitive eff1 any)) (nullable eff2) H0).
      rewrite  (andb_true_iff (nullable (derivitive eff1 f)) (nullable eff2)).
      split. exact (IHeff1 s' f H1). exact H2.
  - intro s'. unfold derivitive. fold derivitive. 
    intro f. unfold nullable. fold nullable. intros.
    assert (temp := orb_prop (nullable (derivitive eff1 any)) (nullable (derivitive eff2 any)) H).
    destruct temp.
    + rewrite  (orb_true_iff (nullable (derivitive eff1 f)) (nullable (derivitive eff2 f))).
      left. exact (IHeff1 s' f H0).
    + rewrite  (orb_true_iff (nullable (derivitive eff1 f)) (nullable (derivitive eff2 f))).
      right. exact (IHeff2 s' f H0).
  - intro s'. unfold derivitive. fold derivitive.
    intro f. unfold nullable. fold nullable. intros.
    destruct (andb_prop (nullable (derivitive eff any)) true H).
    rewrite  (andb_true_iff (nullable (derivitive eff f)) true).
    split. exact (IHeff s' f H0). reflexivity.
Qed.
   
Lemma wildcard_entails_rhs_imply_nullable_rhs:
  forall (rhs: contEff) (f:fstT), 
    entailment 2 [] wildcard rhs = true ->
      nullable (derivitive rhs f) = true.
Proof. 
  intro rhs.  
  unfold entailment. fold entailment. unfold nullable. fold nullable.
  unfold reoccurTRS. unfold derivitive. fold derivitive. unfold normal. fold normal.
  unfold fst. unfold map. unfold fold_left. 
  Search (true && _ = _).
  rewrite andb_true_l.
  unfold nullable. fold nullable. unfold compareEff. fold compareEff.
  rewrite andb_false_l.
  intro f. induction f.
  + case_eq (nullable ( (derivitive rhs any))).
    - intros. exact (nullable_wildcard_any_imply_wildcard_one rhs s (one s) H).
    - intros. discriminate H0.
  + case_eq (nullable ( (derivitive rhs any))).
    - intros. exact (nullable_wildcard_any_imply_wildcard_one rhs s (zero s) H).
    - intros. discriminate H0.
  + case_eq (nullable ( (derivitive rhs any))).
    - intros. reflexivity.
    - intros. discriminate H0.
Qed.


Lemma test: 
  forall (n:string), String.eqb n n = true.
Proof.
  intro n.
  Search (String.eqb _ _ = _).
  exact (String.eqb_refl n).
Qed.


Lemma entailFstOne:
  forall (s1 s2:sigma), compareEvent s1 s2 = true -> entailFst (one s1) (one s2) = true.
Proof.
  intros s1 s2.
  unfold entailFst. intro. exact H.
Qed. 
  

Lemma singleton_entails_rhs_imply_nullable_rhs:
  forall (rhs: contEff) (s:sigma), 
    entailment 2 [] (singleton s) rhs = true ->
      nullable (derivitive rhs (one s)) = true.
Proof. 
  intros rhs s.  
  unfold entailment. fold entailment. unfold nullable. fold nullable.
  unfold reoccurTRS. unfold derivitive. fold derivitive. unfold normal. fold normal.
  unfold fst. unfold map. unfold fold_left. 
  Search (true && _ = _).
  rewrite andb_true_l.
  unfold nullable. fold nullable. unfold compareEff. fold compareEff.
  case_eq (entailFst (one s) (one s)).
  - intro H. 
    unfold nullable. fold nullable. unfold normal. fold normal. unfold compareEff. fold compareEff.
    case_eq (nullable (derivitive rhs (one s))). simpl. intros. reflexivity.
    intros. discriminate H1.
  - unfold entailFst.

    induction s.
    * unfold compareEvent. intro. discriminate H.
    * unfold compareEvent. intro. discriminate H.
Qed.

Lemma not_s_entails_rhs_imply_nullable_rhs:
  forall (rhs: contEff) (s:sigma), 
    entailment 2 [] (not s) rhs = true ->
      nullable (derivitive rhs (zero s)) = true.
Proof. 
  intros rhs s.  
  unfold entailment. unfold nullable. fold nullable.
  unfold fst. fold fst. 
  unfold reoccurTRS.  unfold normal. fold normal.
  unfold map. unfold derivitive. fold derivitive. unfold fold_left.  
  rewrite andb_true_l.
  case_eq (entailFst (zero s) (zero s)).
  - intro H. 
    unfold nullable. fold nullable. unfold normal. fold normal. unfold compareEff. fold compareEff.
    case_eq (nullable (derivitive rhs (zero s))). simpl. intros. reflexivity.
    intros. discriminate H1.
  - unfold entailFst.
    induction s.
    * unfold compareEvent. intro. discriminate H.
    * unfold compareEvent. intro. discriminate H.
Qed.


Lemma bool_trans:
  forall (a b c: bool), a = b  -> a = c -> b = c.
Proof.
  intro a. induction a. 
  - intro b. induction b.
    + intro c. induction c.
      * intros. reflexivity.
      * intros. discriminate H0.
    + intro c. induction c.
      * intros. discriminate H.
      * intros. reflexivity. 
  - intro b. induction b.
    + intro c. induction c.
      * intros. discriminate H.
      * intros. discriminate H.
    + intro c. induction c.
      * intros. discriminate H0. 
      * intros. reflexivity.
Qed. 

Lemma compareEvent_entails :
  forall (s0 s:sigma), 
  compareEvent s0 s = true -> s0 = s.
Proof.
  intro. 
  induction s0.
  - intro. induction s.
    * unfold compareEvent. intro. reflexivity.
    * unfold compareEvent. intro. discriminate H.
  - intro. induction s.
    * unfold compareEvent. intro. discriminate H.
    * unfold compareEvent. intro. reflexivity.
Qed.



Theorem soundnessTRS: 
  forall (lhs: contEff)  (rhs: contEff) (f:fstT), exists n, 
    entailment n [] lhs rhs = true -> 
      entailment n [] (derivitive lhs f) (derivitive rhs f) = true .
Proof.
  intro lhs. induction lhs.
  - intros. unfold derivitive. fold derivitive. exists 1. intro.
    exact (bot_entails_everything (derivitive rhs f)). 
  - intros. unfold derivitive. fold derivitive. exists 1. intro.
    exact (bot_entails_everything (derivitive rhs f)).
  - intros. unfold derivitive. fold derivitive. exists 2.
    intro H. 
    Check (wildcard_entails_rhs_imply_nullable_rhs rhs f H).
    assert (H1:= (wildcard_entails_rhs_imply_nullable_rhs rhs f H)).
    unfold entailment. fold entailment. unfold nullable. fold nullable.
    unfold reoccurTRS.
    case_eq (nullable (derivitive rhs f)). intros.
    + unfold derivitive. fold derivitive. unfold fst. unfold map.
      unfold  fold_left. reflexivity.
    + intro.
      assert (dis:= bool_trans (nullable (derivitive rhs f)) true false H1 H0).
      discriminate dis.
  - intros. unfold derivitive. fold derivitive. exists 1. intro.
    exact (bot_entails_everything (derivitive rhs f)).
  - intros. 
    unfold derivitive. fold derivitive. exists 2. 
    intro H. 
    assert (H1:= (singleton_entails_rhs_imply_nullable_rhs rhs s H)).
    + induction f.
      * unfold entailFst.
        case_eq (compareEvent s0 s).
        -- intros.  unfold entailment. unfold nullable. fold nullable.
           assert (H_temp := compareEvent_entails s0 s H0).
           rewrite H_temp.
           rewrite H1.
           unfold reoccurTRS. fold reoccurTRS.
           unfold fst. fold fst. unfold map. unfold fold_left. reflexivity.
        -- intros.
           exact (bot_entails_everything (derivitive rhs (one s0))). 
      * unfold entailFst.
           exact (bot_entails_everything (derivitive rhs (one s0))).
      * unfold entailFst. 
         exact (bot_entails_everything (derivitive rhs any)).
  - intros. 
    unfold derivitive. fold derivitive. exists 2. 
    intro H. 
    assert (H1:= (not_s_entails_rhs_imply_nullable_rhs rhs s H)).
    + induction f.
      * unfold entailFst.
        exact (bot_entails_everything (derivitive rhs (one s0))).
      * unfold entailFst.
        case_eq (compareEvent s0 s).
        -- intros.  unfold entailment. unfold nullable. fold nullable.
           assert (H_temp := compareEvent_entails s0 s H0).
           rewrite H_temp.
           unfold reoccurTRS. rewrite H1. 
           unfold fst. fold fst. unfold map. unfold fold_left. reflexivity.
       -- intros. 
          exact (bot_entails_everything (derivitive rhs (one s0))). 
      * unfold entailFst.
        exact (bot_entails_everything (derivitive rhs any)).
  - intro rhs. induction rhs. 
    + unfold entailment. 
  - admit.

    
  -  intros. exists 2.
     unfold entailment.  unfold nullable. fold nullable.
     unfold reoccurTRS.

        
        
    
Qed.


Definition eff1 : contEff := emp.
Definition eff2 : contEff := {{[("A", one)]}}.
Definition eff3 : contEff := waiting "A".

Compute (entailmentShell eff3 eff2).

Compute (entailmentShell eff2 eff3).


Compute (entailmentShell (kleene eff2) (kleene eff2)).


