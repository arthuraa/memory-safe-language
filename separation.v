Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.choice.
Require Import Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg.
Require Import MathComp.generic_quotient.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.fperm.
Require Import CoqUtils.nominal CoqUtils.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Definition int_partOrdMixin :=
  (@PartOrdMixin int <=%R (@Num.Theory.lerr _) (@Num.Theory.ler_trans _)
                          (@Num.Theory.ler_anti _))%R.

Canonical int_partOrdType :=
  Eval hnf in PartOrdType int int_partOrdMixin.

Definition int_ordMixin :=
  @OrdMixin [partOrdType of int] (@Num.Theory.ler_total _).

Canonical int_ordType :=
  Eval hnf in OrdType int int_ordMixin.

Canonical int_nominalType :=
  Eval hnf in [nominalType for int by //].
Canonical int_trivialNominalType :=
  Eval hnf in [trivialNominalType for int].

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Inductive expr :=
| Var of string
| Num of int
| Binop of binop & expr & expr
| ENil
| Cast of expr.

Inductive com : Type :=
| Assn of string & expr
| Load of string & expr
| Store of expr & expr
| Alloc of string & expr
| Free of expr
| Skip
| Seq of com & com
| If of expr & com & com
| While of expr & com.

Definition ptr : Type := (name * int)%type.

Inductive value :=
| VBool of bool
| VNum  of int
| VPtr  of ptr
| VNil.

Definition is_vnat v :=
  if v is VNum (Posz _) then true else false.

Definition sum_of_value v :=
  match v with
  | VBool b => inl b
  | VNum n => inr (inl n)
  | VPtr p => inr (inr (inl p))
  | VNil => inr (inr (inr tt))
  end.

Definition value_of_sum v :=
  match v with
  | inl b => VBool b
  | inr (inl n) => VNum n
  | inr (inr (inl p)) => VPtr p
  | inr (inr (inr tt)) => VNil
  end.

Lemma sum_of_valueK : cancel sum_of_value value_of_sum.
Proof. by case. Qed.
Lemma value_of_sumK : cancel value_of_sum sum_of_value.
Proof. by do ![case=>//]. Qed.
Definition value_eqMixin := CanEqMixin sum_of_valueK.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.
Definition value_choiceMixin := CanChoiceMixin sum_of_valueK.
Canonical value_choiceType := Eval hnf in ChoiceType value value_choiceMixin.
Definition value_partOrdMixin := CanPartOrdMixin sum_of_valueK.
Canonical value_partOrdType :=
  Eval hnf in PartOrdType value value_partOrdMixin.
Definition value_ordMixin := CanOrdMixin sum_of_valueK.
Canonical value_ordType := Eval hnf in OrdType value value_ordMixin.
Definition value_nominalMixin := BijNominalMixin sum_of_valueK value_of_sumK.
Canonical value_nominalType :=
  Eval hnf in NominalType value value_nominalMixin.

Lemma renamevE pm v :
  rename pm v =
  match v with
  | VBool b => VBool b
  | VNum n => VNum n
  | VPtr p => VPtr (rename pm p)
  | VNil => VNil
  end.
Proof. by case: v. Qed.

Lemma namesvE v :
  names v =
  match v with
  | VPtr p => fset1 p.1
  | _ => fset0
  end.
Proof.
case: v=> [b|n|[i n]|] //=.
rewrite /names /= /bij_names /=; do ![rewrite /names /=].
by rewrite /prod_names fsetU0.
Qed.

Definition locals := {partmap string -> value}.
Definition heap := {partmap name * int -> value}.

Implicit Types (ls : locals) (h : heap).

Definition init_block h b n :=
  unionm (mkpartmapf (fun _ => VNum 0) [seq (b, Posz i) | i <- iota 0 n]) h.

Definition alloc_fun ls h n :=
  locked (let b := fresh (names (ls, h)) in (b, init_block h b n)).

Definition free_fun h i :=
  locked
  (if i \in domm (currym h) then
     Some (filterm (fun p _ => p.1 != i) h)
   else None).

Definition eval_binop b v1 v2 :=
  match b, v1, v2 with
  | Add, VNum n1, VNum n2 => VNum (n1 + n2)
  | Add, VPtr p, VNum n
  | Add, VNum n, VPtr p => VPtr (p.1, p.2 + n)
  | Add, _, _ => VNil
  | Sub, VNum n1, VNum n2 => VNum (n1 - n2)
  | Sub, VPtr p, VNum n => VPtr (p.1, p.2 - n)
  | Sub, _, _ => VNil
  | Mul, VNum n1, VNum n2 => VNum (n1 * n2)
  | Mul, _, _ => VNil
  | Eq, _, _ => VBool (v1 == v2)
  | Leq, VNum n1, VNum n2 => VBool (n1 <= n2)
  | Leq, _, _ => VNil
  | And, VBool b1, VBool b2 => VBool (b1 && b2)
  | And, _, _ => VNil
  | Or, VBool b1, VBool b2 => VBool (b1 || b2)
  | Or, _, _ => VNil
  end%R.

Fixpoint eval_expr safe ls e :=
  match e with
  | Var x => odflt VNil (ls x)
  | Num n => VNum n
  | Binop b e1 e2 => eval_binop b (eval_expr safe ls e1) (eval_expr safe ls e2)
  | ENil => VNil
  | Cast e =>
    let v := eval_expr safe ls e in
    if safe then v
    else if eval_expr safe ls e is VPtr p then VNum (val p.1) else VNil
  end.

Section Result.

Variable T : Type.

Inductive result :=
| Done of T
| Error
| NotYet.

Definition sum_of_result r :=
  match r with
  | Done x => inl x
  | Error => inr true
  | NotYet => inr false
  end.

Definition result_of_sum r :=
  match r with
  | inl x => Done x
  | inr true => Error
  | inr false => NotYet
  end.

Lemma sum_of_resultK : cancel sum_of_result result_of_sum.
Proof. by case. Qed.
Lemma result_of_sumK : cancel result_of_sum sum_of_result.
Proof. by do ![case=>//]. Qed.

Definition result_of_option r :=
  if r is Some x then Done x else Error.

End Result.

Arguments Error {_}.
Arguments NotYet {_}.

Definition result_eqMixin (T : eqType) :=
  CanEqMixin (@sum_of_resultK T).
Canonical result_eqType (T : eqType) :=
  Eval hnf in EqType (result T) (result_eqMixin T).
Definition result_choiceMixin (T : choiceType) :=
  CanChoiceMixin (@sum_of_resultK T).
Canonical result_choiceType (T : choiceType) :=
  Eval hnf in ChoiceType (result T) (result_choiceMixin T).
Definition result_partOrdMixin (T : partOrdType) :=
  CanPartOrdMixin (@sum_of_resultK T).
Canonical result_partOrdType (T : partOrdType) :=
  Eval hnf in PartOrdType (result T) (result_partOrdMixin T).
Definition result_ordMixin (T : ordType) :=
  CanOrdMixin (@sum_of_resultK T).
Canonical result_ordType (T : ordType) :=
  Eval hnf in OrdType (result T) (result_ordMixin T).
Definition result_nominalMixin (T : nominalType) :=
  BijNominalMixin (@sum_of_resultK T) (@result_of_sumK T).
Canonical result_nominalType (T : nominalType) :=
  Eval hnf in NominalType (result T) (result_nominalMixin T).

CoInductive sem T := Sem {
  assn : string -> expr -> T -> T;
  load : string -> expr -> T -> option T;
  store : expr -> expr -> T -> option T;
  alloc : string -> expr -> T -> option T;
  free : expr -> T -> option T;
  eval_cond : expr -> T -> option bool
}.

Fixpoint eval_com T (S : sem T) s c k :=
  if k is S k' then
    match c with
    | Assn x e => Done (assn S x e s)

    | Load x e => result_of_option (load S x e s)

    | Store e e' => result_of_option (store S e e' s)

    | Alloc x e => result_of_option (alloc S x e s)

    | Free e => result_of_option (free S e s)

    | Skip => Done s

    | Seq c1 c2 =>
      let r1 := eval_com S s c1 k' in
      if r1 is Done s' then
        eval_com S s' c2 k'
      else r1

    | If e ct ce =>
      if eval_cond S e s is Some b then
        eval_com S s (if b then ct else ce) k'
      else Error

    | While e c =>
      if eval_cond S e s is Some b then
        eval_com S s (if b then Seq c (While e c) else Skip) k'
      else Error
    end
  else NotYet.

Definition refine_result (T : eqType) (r1 r2 : result T) :=
  (r1 == NotYet) || (r1 == r2).

Lemma eval_com_leq (T : eqType) (S : sem T) s c k k' :
  (k <= k')%N ->
  refine_result (eval_com S s c k) (eval_com S s c k').
Proof.
move=> Pk; elim: k' k Pk s c => [|k' IH] [|k] // /IH {IH} IH s.
rewrite /refine_result.
case=> [x e|x e|e e'|x e|e| |c1 c2|e ct ce|e c] /=; try by rewrite eqxx ?orbT.
- case/orP: (IH s c1) => [/eqP -> //|/eqP ->].
  case: (eval_com _ _ c1 _) => [s'| |] //=.
  by eauto.
- by case: (eval_cond S e s) => [b|] //=; eauto.
by case: (eval_cond S e s) => [b|] //=; eauto.
Qed.

Definition basic_sem safe : sem (locals * heap) := {|
  assn x e s :=
    (setm s.1 x (eval_expr safe s.1 e), s.2);

  load x e := fun s : locals * heap =>
    if eval_expr safe s.1 e is VPtr p then
      if s.2 p is Some v then Some (setm s.1 x v, s.2)
      else None
    else None;

  store e e' s :=
    if eval_expr safe s.1 e is VPtr p then
      if updm s.2 p (eval_expr safe s.1 e') is Some h' then Some (s.1, h')
      else None
    else None;

  alloc x e s :=
    if eval_expr safe s.1 e is VNum (Posz n) then
      let res := alloc_fun s.1 s.2 n in
      Some (setm s.1 x (VPtr (res.1, 0 : int)), res.2)
    else None;

  free e s :=
    if eval_expr safe s.1 e is VPtr p then
      if p.2 == 0 then
        if free_fun s.2 p.1 is Some h' then Some (s.1, h')
        else None
      else None
    else None;

  eval_cond e s :=
    if eval_expr safe s.1 e is VBool b then Some b
    else None

|}.

Lemma rename_eval_binop pm b v1 v2 :
  rename pm (eval_binop b v1 v2) =
  eval_binop b (rename pm v1) (rename pm v2).
Proof.
case: b v1 v2 => [] [b1|n1|p1|] [b2|n2|p2|] //=.
by rewrite (can_eq (renameK pm)).
Qed.

Lemma rename_eval_expr pm ls e :
  rename pm (eval_expr true ls e) =
  eval_expr true (rename pm ls) e.
Proof.
elim: e=> [x|n|b e1 IH1 e2 IH2| |e IH] //=.
  rewrite renamemE /= renameT.
  by case: (ls x)=> [v|] //=.
by rewrite rename_eval_binop IH1 IH2.
Qed.

Lemma renamerE (T : nominalType) pm (r : result T) :
  rename pm r =
  match r with
  | Done x => Done (rename pm x)
  | Error => Error
  | NotYet => NotYet
  end.
Proof. by case: r. Qed.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Lemma fdisjoint_names_domm h1 h2 :
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  fdisjoint (domm h1) (domm h2).
Proof.
move=> /fdisjointP dis; apply/fdisjointP=> p Pp.
have /dis Pi: p.1 \in names (domm h1).
  by apply/namesfsP; exists p=> //=; apply/namesnP.
apply: contra Pi=> Pi; apply/namesfsP; exists p=> //.
by apply/namesnP.
Qed.

Lemma rename_free_fun pm h i :
  rename pm (free_fun h i) = free_fun (rename pm h) (rename pm i).
Proof.
rewrite /free_fun; unlock.
rewrite -renamem_curry -renamem_dom mem_imfset_inj; last first.
  by move=> ??; apply: rename_inj.
case: ifP=> //= _.
rewrite renameoE /= renamem_filter; congr Some.
apply: eq_filterm=> p _ /=.
by rewrite (can2_eq (renameKV pm) (renameK pm)).
Qed.

Fixpoint vars_e e :=
  match e with
  | Var x => fset1 x
  | Num _ => fset0
  | Binop _ e1 e2 => vars_e e1 :|: vars_e e2
  | ENil => fset0
  | Cast e => vars_e e
  end.

Fixpoint vars_c c :=
  match c with
  | Assn x e => x |: vars_e e
  | Load x e => x |: vars_e e
  | Store e e' => vars_e e :|: vars_e e'
  | Alloc x e => x |: vars_e e
  | Free e => vars_e e
  | Skip => fset0
  | Seq c1 c2 => vars_c c1 :|: vars_c c2
  | If e ct ce => vars_e e :|: vars_c ct :|: vars_c ce
  | While e c => vars_e e :|: vars_c c
  end.

Lemma eval_expr_unionm safe ls1 ls2 e :
  fsubset (vars_e e) (domm ls1) ->
  eval_expr safe (unionm ls1 ls2) e =
  eval_expr safe ls1 e.
Proof.
elim: e => [x|n|b e1 IH1 e2 IH2| |e IH] //=.
- by rewrite fsub1set unionmE => /dommP [v ->].
- by rewrite fsubUset=> /andP [/IH1 {IH1} -> /IH2 {IH2} ->].
by case: safe IH=> // IH sub; rewrite IH.
Qed.

Lemma eval_binop_names b v1 v2 :
  fsubset (names (eval_binop b v1 v2)) (names (v1, v2)).
Proof.
case: b v1 v2=> [] [b1|n1|p1|] [b2|n2|p2|] //=; try by rewrite fsub0set.
- by rewrite fsubsetU //= !namesvE fsubsetxx.
- by rewrite fsubsetU //= !namesvE fsubsetxx.
by rewrite fsubsetU //= !namesvE fsubsetxx.
Qed.

Lemma eval_expr_names safe ls e :
  fsubset (names (eval_expr safe ls e)) (names ls).
Proof.
elim: e=> [x|n|b e1 IH1 e2 IH2| |e IH] //=; try by rewrite fsub0set.
- case get_x: (ls x) => [[b|n|p|]|] //=; try by rewrite fsub0set.
  apply/fsubsetP=> i; rewrite namesvE => /fset1P -> {i}.
  apply/namesmP; eapply PMFreeNamesVal; eauto.
  by rewrite namesvE; apply/namesnP.
- by rewrite (fsubset_trans (eval_binop_names b _ _)) // fsubUset IH1 IH2.
case: safe IH=> //.
by case: (eval_expr _ _ _)=> [b|n|p|]; rewrite fsub0set.
Qed.

Lemma names_init_block h i n :
  fsubset (names (init_block h i n)) (i |: names h).
Proof.
rewrite (fsubset_trans (namesm_union _ _)) // fsetU1E fsetSU //.
apply/fsubsetP=> i'; case/namesmP=> [p v|p v]; rewrite mkpartmapfE;
case: ifP=> // /mapP [n' Pn'].
  by move=> -> {p} _; rewrite in_fsetU in_fset0 orbF.
by move=> _ [<-].
Qed.

Lemma init_block_unionm h1 h2 i n :
  init_block (unionm h1 h2) i n = unionm (init_block h1 i n) h2.
Proof. by rewrite /init_block unionmA. Qed.

Definition state := {bound locals * heap}.

Definition stateu : state -> state -> state :=
  mapb2 (fun s1 s2 => (unionm s1.1 s2.1, unionm s1.2 s2.2)).

Notation "s1 * s2" := (stateu s1 s2) : state_scope.

Local Open Scope state_scope.

Lemma stateuE A1 ls1 h1 A2 ls2 h2 :
  mutfresh A1 (ls1, h1) A2 (ls2, h2) ->
  mask A1 (ls1, h1) * mask A2 (ls2, h2) =
  mask (A1 :|: A2) (unionm ls1 ls2, unionm h1 h2).
Proof.
move=> mf; rewrite /stateu /=.
rewrite mapb2E //= => {ls1 h1 ls2 h2 mf} /= pm [[ls1 h1] [ls2 h2]] /=.
by rewrite !renamepE !renamem_union.
Qed.

Lemma rename_stateu pm (s1 s2 : state) :
  rename pm (s1 * s2) = rename pm s1 * rename pm s2.
Proof.
rewrite /= rename_mapb2 //= => {pm s1 s2} pm /= [[ls1 h1] [ls2 h2]] /=.
by rewrite !renamepE !renamem_union.
Qed.

Definition vars_s (s : state) : {fset string} :=
  locked (@expose _ \o mapb (fun s => domm s.1)) s.

Lemma vars_sE A ls h : vars_s (mask A (ls, h)) = domm ls.
Proof.
rewrite /vars_s /= -lock /= mapbE ?exposeE //.
by move=> pm /= {ls h} [ls h] /=; rewrite -renamem_dom.
Qed.

Definition emp : state := mask fset0 (emptym, emptym).

Lemma stateu0s : left_id emp stateu.
Proof.
apply: bound_left_id=> /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls h] /=; rewrite !union0m.
Qed.

Lemma stateus0 : right_id emp stateu.
Proof.
apply: bound_right_id=> /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls h] /=; rewrite !unionm0.
Qed.

Lemma stateuA : associative stateu.
Proof.
apply: bound_associative => /=.
  move=> /= s [[ls1 h1] [ls2 h2]] /=.
  by rewrite renamepE /= !renamem_union.
by move=> [ls1 h1] [ls2 h2] [ls3 h3] /=; rewrite !unionmA.
Qed.

Definition objs (s : state) : {fset name} :=
  names (mapb (fun s => domm s.2) s).

Lemma objsE A ls h : objs (mask A (ls, h)) = A :&: names (domm h).
Proof.
rewrite /objs /= mapbE /= 1?maskE 1?namesbE ?fsubsetIr //.
by move=> pm {ls h} /= [ls h]; rewrite renamem_dom.
Qed.

Lemma mutfresh_eval_expr A1 ls1 h1 A2 ls2 h2 e p :
  mutfresh A1 (ls1, h1) A2 (ls2, h2) ->
  eval_expr true ls1 e = VPtr p ->
  A2 :&: names (domm h2) = fset0 ->
  h2 p = None.
Proof.
move=> mf eval_e dis; case get_p: (h2 p)=> [v|] //.
move: (eval_expr_names true ls1 e); rewrite eval_e namesvE.
have inNh2: p.1 \in names (domm h2).
  apply/namesfsP; exists p; first by rewrite mem_domm get_p.
  by apply/fsetUP; left; apply/namesnP.
rewrite fsub1set=> inNls1.
suff: p.1 \in A2 :&: names (domm h2) by rewrite dis.
rewrite in_fsetI inNh2 andbT.
have inNs1: p.1 \in names (ls1, h1) by rewrite in_fsetU inNls1.
have inNs2: p.1 \in names (ls2, h2) by rewrite !in_fsetU inNh2 orbT.
case/and3P: mf=> [_ _ /fsubsetP/(_ p.1)].
by rewrite in_fsetI inNs1 inNs2=> /(_ erefl) => /fsetIP [].
Qed.

Definition bound_assn (x : string) (e : expr) : state -> state :=
  mapb (assn (basic_sem true) x e).

Lemma rename_assn x e : equivariant (assn (basic_sem true) x e).
Proof.
move=> pm /= [ls h] /=.
by rewrite renamepE /= renamem_set rename_eval_expr.
Qed.

Lemma bound_assnE x e A s :
  bound_assn x e (mask A s) = mask A (assn (basic_sem true) x e s).
Proof. by rewrite /bound_assn mapbE //; apply/rename_assn. Qed.

Lemma rename_bound_assn x e : equivariant (bound_assn x e).
Proof. by rewrite /bound_assn; apply/rename_mapb/rename_assn. Qed.

Lemma bound_assn_frame x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_assn x e s1 * s2 = bound_assn x e (s1 * s2).
Proof.
case: s1 s2 / (bound2P s1 s2) => /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE bound_assnE.
have sub1': fsubset (names (setm ls1 x (eval_expr true ls1 e))) (names ls1).
  apply/(fsubset_trans (namesm_set _ _ _)).
  by rewrite fsetU0 fsubUset fsubsetxx /= eval_expr_names.
rewrite stateuE //=; first last.
  apply/(mutfreshEl (rename_assn _ _) mf).
rewrite fsubU1set=> /andP [inD inV]; rewrite stateuE //.
by rewrite bound_assnE //= setm_union eval_expr_unionm.
Qed.

Definition bound_load x e : state -> option state :=
  @obound _ \o mapb (load (basic_sem true) x e).

Lemma rename_load x e : equivariant (load (basic_sem true) x e).
Proof.
move=> /= pm [ls1 h1] /=.
rewrite -rename_eval_expr; case: eval_expr=> [| |p|] //=.
rewrite renamemE renameK; case: (h1 p)=> [v|] //=.
by rewrite renameoE /= renamepE /= renamem_set.
Qed.

Lemma bound_loadE x e A s :
  bound_load x e (mask A s) = omap (mask A) (load (basic_sem true) x e s).
Proof.
rewrite /bound_load /= mapbE; last exact: rename_load.
by rewrite oboundE.
Qed.

Lemma rename_bound_load x e : equivariant (bound_load x e).
Proof.
apply/equivariant_comp.
  by apply/rename_obound.
by apply/rename_mapb/rename_load.
Qed.

Lemma bound_load_frame_ok x e s1 s1' s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_load x e s1 = Some s1' ->
  bound_load x e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set=> /andP [x_in vars].
rewrite !bound_loadE /=; move: (mutfreshEl (rename_load x e) mf)=> /=.
rewrite stateuE // bound_loadE /= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite unionmE.
case get_p: (h1 p)=> [v|] //= mf'.
by move => - [<-]; rewrite stateuE // ?setm_union.
Qed.

Lemma bound_load_frame_error x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  objs s2 = fset0 ->
  bound_load x e s1 = None ->
  bound_load x e (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set=> /andP [x_in vars].
rewrite objsE=> dis; rewrite bound_loadE /=.
move: (mutfreshEl (rename_load x e) mf)=> /=.
rewrite stateuE // bound_loadE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite unionmE.
case get_p: (h1 p)=> [v|] //= mf' _ {get_p}.
by rewrite (mutfresh_eval_expr mf eval_e).
Qed.

(* Store *)

Definition bound_store e e' : state -> option state :=
  @obound _ \o mapb (store (basic_sem true) e e').

Lemma rename_store e e' : equivariant (store (basic_sem true) e e').
Proof.
move=> /= pm [ls1 h1] /=.
rewrite -rename_eval_expr; case: eval_expr=> [| |p|] //=.
rewrite /updm renamemE renameK; case: (h1 p)=> [v|] //=.
by rewrite renameoE /= renamepE /= renamem_set rename_eval_expr.
Qed.

Lemma bound_storeE e e' A s :
  bound_store e e' (mask A s) = omap (mask A) (store (basic_sem true) e e' s).
Proof.
rewrite /bound_store /= mapbE; last by apply: rename_store.
by rewrite oboundE.
Qed.

Lemma rename_bound_store e e' : equivariant (bound_store e e').
Proof.
apply/equivariant_comp; first by apply/rename_obound.
by apply/rename_mapb/rename_store.
Qed.

Lemma bound_store_frame_ok e e' s1 s1' s2 :
  fsubset (vars_e e :|: vars_e e') (vars_s s1) ->
  bound_store e e' s1 = Some s1' ->
  bound_store e e' (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubUset=> /andP [vars vars'].
rewrite bound_storeE.
move: (mutfreshEl (rename_store e e') mf)=> /=.
rewrite stateuE // bound_storeE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite /updm unionmE.
case get_p: (h1 p)=> [v|] //= mf'.
by move => - [<-]; rewrite stateuE // ?setm_union eval_expr_unionm.
Qed.

Lemma bound_store_frame_error e e' s1 s2 :
  fsubset (vars_e e :|: vars_e e') (vars_s s1) ->
  objs s2 = fset0 ->
  bound_store e e' s1 = None ->
  bound_store e e' (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubUset=> /andP [vars vars'].
rewrite objsE=> dis; rewrite bound_storeE /=.
move: (mutfreshEl (rename_store e e') mf)=> /=.
rewrite stateuE // bound_storeE //= eval_expr_unionm //.
case eval_e: eval_expr => [| |p|] //; rewrite /updm unionmE.
case get_p: (h1 p)=> [v|] //= mf' _.
by rewrite (mutfresh_eval_expr mf eval_e).
Qed.

Definition locval (x : string) (v : value) : state :=
  locked (mask (names v) (setm emptym x v, emptym)).

Lemma names_locval x v : names (locval x v) = names v.
Proof.
rewrite /locval -lock namesbE //; apply/fsubsetU/orP; left=> /=.
apply/fsubsetP=> n inN; apply/namesmP.
have get_x: setm emptym x v x = Some v by rewrite setmE eqxx.
eapply PMFreeNamesVal; eauto.
Qed.

Lemma rename_locval s x v :
  rename s (locval x v) = locval x (rename s v).
Proof.
rewrite /locval -!lock renamebE names_rename renamefsE; congr mask.
by rewrite renamepE /= renamem_set renameT !renamem_empty.
Qed.

Definition blockat (i : name) (vs : seq value) : state :=
  locked (mask (i |: names vs)
               (emptym, mkpartmapf (fun p => nth VNil vs (absz p.2))
                                   [seq (i, Posz n) | n <- iota 0 (size vs)])).

Lemma names_blockat i vs :
  names (blockat i vs) =
  if nilp vs then fset0 else i |: names vs.
Proof.
rewrite /blockat -lock; case: ifPn=> [/nilP -> /=|vs0n].
  rewrite maskE fsetIUr /= !namesm_empty !fsetI0 fsetU0 namesbE //.
  exact: fsub0set.
rewrite namesbE //; apply/fsubsetU/orP; right=> /=.
apply/fsubsetP=> i' /fsetU1P [{i'}->|].
  rewrite namesmE; apply/fsetUP; left; apply/namesfsP.
  exists (i, Posz 0); last by rewrite in_fsetU in_fset1 eqxx.
  rewrite mem_domm mkpartmapE.
  by case: vs vs0n=> [|v vs] //= _; rewrite eqxx.
case/namessP=> v in_vs inN.
rewrite namesmE; apply/fsetUP; right; apply/namesfsP.
exists v=> //; apply/codommP.
exists (i, Posz (find (pred1 v) vs)).
rewrite mkpartmapfE mem_map; last by move=> n m /= [<-].
rewrite mem_iota leq0n /= add0n -has_find.
have in_vs' : has (pred1 v) vs by rewrite has_pred1.
by rewrite in_vs'; congr Some; apply/eqP/(nth_find VNil in_vs').
Qed.

Lemma rename_blockat s i vs :
  rename s (blockat i vs) = blockat (s i) (rename s vs).
Proof.
rewrite /blockat -!lock renamebE renamefsE imfsetU1 names_rename.
congr mask; rewrite renamepE /= renamem_empty; congr pair.
rewrite renamem_mkpartmapf; apply/eq_partmap=> /= - [i' p].
rewrite !mkpartmapfE renamesE -map_comp /= renameT renames_nth.
by rewrite renamevE size_map.
Qed.

Definition newblock (x : string) (n : nat) : state :=
  new fset0 (fun i => locval x (VPtr (i, Posz 0)) *
                      blockat i (nseq n (VNum (Posz 0)))).

Lemma names_newblock x n : names (newblock x n) = fset0.
Proof.
rewrite /newblock; move: (fresh _) (freshP fset0)=> i nin.
have equi: equivariant (fun i => locval x (VPtr (i, Posz 0)) *
                                 blockat i (nseq n (VNum 0))).
  move=> {i nin} /= s i.
  rewrite rename_stateu rename_locval rename_blockat renamevE.
  have /eq_in_map e: {in nseq n (VNum 0), rename s =1 id}.
    by move=> v /nseqP [-> _].
  by rewrite renamesE e map_id.
rewrite (newE nin); last by apply/equivariant_finsupp.
rewrite names_hide; apply/eqP; rewrite -fsubset0; apply/fsubsetP=> i'.
move/fsubsetP: (equivariant_names equi i)=> sub.
rewrite in_fsetD1=> /andP [ne /sub/namesnP ?]; subst i'.
by rewrite eqxx in ne.
Qed.

Definition eval_nat e (s : locals * heap) :=
  if eval_expr true s.1 e is VNum (Posz n) then Some n
  else None.

Lemma rename_eval_nat e pm s :
  rename pm (eval_nat e s) = eval_nat e (rename pm s).
Proof.
rewrite /eval_nat -rename_eval_expr; case: eval_expr=> //.
by case=> [n|] //.
Qed.

Definition bound_eval_nat e : state -> option nat :=
  locked (@expose _ \o mapb (eval_nat e)).

Lemma bound_eval_natE e A s : bound_eval_nat e (mask A s) = eval_nat e s.
Proof.
rewrite /bound_eval_nat -lock /=.
rewrite mapbE; last exact: rename_eval_nat.
by case: eval_nat=> [n|] //; rewrite exposeE.
Qed.

Lemma rename_bound_eval_nat e : equivariant (bound_eval_nat e).
Proof.
rewrite /bound_eval_nat -lock; apply/equivariant_comp.
  apply/rename_expose.
by apply/rename_mapb/rename_eval_nat.
Qed.

Definition bound_alloc x e (s : state) : option state :=
  if bound_eval_nat e s is Some n then Some (newblock x n * s)
  else None.

Lemma rename_bound_alloc x e : equivariant (bound_alloc x e).
Proof.
move=> pm /= s; rewrite /bound_alloc -rename_bound_eval_nat.
case: bound_eval_nat=> [n|] //=.
rewrite renameoE /= rename_stateu renameT; congr Some; congr stateu.
by apply/names0P/eqP/names_newblock.
Qed.

Lemma bound_alloc_ok x e s1 s1' s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_alloc x e s1 = Some s1' ->
  bound_alloc x e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set => /andP [x_in vars].
rewrite /bound_alloc {1}stateuE // 2!bound_eval_natE /eval_nat /=.
rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] // [<-].
by rewrite stateuA.
Qed.

Lemma bound_alloc_error x e s1 s2 :
  fsubset (x |: vars_e e) (vars_s s1) ->
  bound_alloc x e s1 = None ->
  bound_alloc x e (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE fsubU1set => /andP [x_in vars].
rewrite /bound_alloc {1}stateuE // 2!bound_eval_natE /eval_nat /=.
by rewrite eval_expr_unionm //; case: eval_expr=> [|[n|]| |] // [<-].
Qed.

Definition bound_free e :=
  locked (@obound _ \o mapb (free (basic_sem true) e)).

Lemma rename_free e : equivariant (free (basic_sem true) e).
Proof.
move=> /= s [ls h] /=; rewrite -rename_eval_expr.
case: eval_expr=> [| |p|] //=; rewrite renameT.
case: ifP=> // _; rewrite -rename_free_fun.
by case: (free_fun _ _)=> [h'|] //=.
Qed.

Lemma bound_freeE e A s :
  bound_free e (mask A s) = omap (mask A) (free (basic_sem true) e s).
Proof.
rewrite /bound_free -lock /= mapbE; last exact: rename_free.
by rewrite oboundE.
Qed.

Lemma rename_bound_free e : equivariant (bound_free e).
Proof.
move=> pm /= s; rewrite /bound_free -lock.
apply: equivariant_comp; first exact: rename_obound.
by apply/rename_mapb/rename_free.
Qed.

Lemma bound_free_ok e s1 s1' s2 :
  fsubset (vars_e e) (vars_s s1) ->
  fdisjoint (objs s1) (objs s2) ->
  bound_free e s1 = Some s1' ->
  bound_free e (s1 * s2) = Some (s1' * s2).
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE !objsE => vars dis.
rewrite bound_freeE {1}stateuE // /= bound_freeE /= eval_expr_unionm //.
case eval_e: eval_expr=> [| |p|] //=.
case: ifP=> //= _; rewrite /free_fun -!lock.
rewrite (domm_curry (unionm _ _)) domm_union imfsetU in_fsetU.
rewrite -domm_curry; case: ifP=> //= inD [<-]; congr Some.
rewrite stateuE.
  congr mask; congr pair.
  have dis_h: fdisjoint (names (domm h1)) (names (domm h2)).
    rewrite /fdisjoint -fsubset0; apply/fsubsetP=> n /fsetIP [inD1 inD2].
    case/and3P: mf=> [_ _ /fsubsetP/(_ n)].
    rewrite in_fsetI in_fsetU /= [in X in _ || X]in_fsetU inD1 orbT /=.
    rewrite in_fsetU /= [in X in _ || X]in_fsetU inD2 orbT /= => /(_ erefl).
    case/fsetIP=> [inA1 inA2]; move/eqP: dis=> <-; rewrite !in_fsetI -!andbA.
    by apply/and4P; split.
  rewrite filterm_union //; last by apply/fdisjoint_names_domm.
  congr unionm; apply/eq_partmap=> p'; rewrite filtermE.
  case get_p': (h2 _) => [v|] //=.
  have [Pe|] //= := altP eqP.
  have: p.1 \in names (domm h1).
    move: inD; rewrite domm_curry=> /imfsetP [p'' inD ->].
    by apply/namesfsP; exists p''; last by apply/namesnP.
  move=> /(fdisjointP _ _ dis_h _); rewrite -{}Pe (_ : p'.1 \in _ = true) //.
  apply/namesfsP; exists p'; last by apply/namesnP.
  by apply/dommP; eauto.
apply/(mutfreshS mf); last exact: fsubsetxx.
by apply/fsetUS/namesm_filter.
Qed.

Lemma bound_free_error e s1 s2 :
  fsubset (vars_e e) (vars_s s1) ->
  objs s2 = fset0 ->
  bound_free e s1 = None ->
  bound_free e (s1 * s2) = None.
Proof.
case: s1 s2 / bound2P=> /= [A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite vars_sE !objsE => vars dis.
rewrite bound_freeE /= {1}stateuE //= bound_freeE /= eval_expr_unionm //.
case eval_e: eval_expr=> [| |p|] //=.
case: ifP=> //= _; rewrite /free_fun -!lock.
rewrite (domm_curry (unionm _ _)) domm_union imfsetU in_fsetU.
rewrite -domm_curry; case: ifPn=> //= ninD _.
case: ifP=> //= /imfsetP [p' inD ep].
have /and3P [_ _ /fsubsetP/(_ p.1)]: mutfresh A1 ls1 A2 h2.
  by apply/(mutfreshS mf); [apply/fsubsetUl|apply/fsubsetUr].
have inL: p.1 \in names ls1.
  move/fsubsetP: (eval_expr_names true ls1 e); apply.
  by rewrite eval_e in_fsetU; apply/orP; left; apply/namesnP.
have inH: p.1 \in names (domm h2).
  rewrite ep; apply/namesfsP; exists p'=> //.
  by apply/fsetUP; left; apply/namesnP.
rewrite in_fsetI inL in_fsetU inH /= => /(_ erefl)/fsetIP [_ inA].
have: p.1 \in A2 :&: names (domm h2) by apply/fsetIP; split.
by rewrite dis in_fset0.
Qed.

Definition bound_eval_cond e :=
  locked (@expose _ \o mapb (eval_cond (basic_sem true) e)).

Lemma rename_eval_cond e : equivariant (eval_cond (basic_sem true) e).
Proof.
move=> pm [ls h]; rewrite /= -rename_eval_expr.
by case: eval_expr=> //.
Qed.

Lemma bound_eval_condE e A s :
  bound_eval_cond e (mask A s) =
  if eval_expr true s.1 e is VBool b then Some b
  else None.
Proof.
rewrite /bound_eval_cond -lock /= mapbE; last exact: rename_eval_cond.
by rewrite exposeE.
Qed.

Lemma rename_bound_eval_cond e : equivariant (bound_eval_cond e).
Proof.
rewrite /bound_eval_cond -lock.
apply/equivariant_comp.
  by apply/rename_expose.
apply/rename_mapb/rename_eval_cond.
Qed.

Definition bound_sem : sem state := {|
  assn := bound_assn;
  load := bound_load;
  store := bound_store;
  alloc := bound_alloc;
  free := bound_free;
  eval_cond := bound_eval_cond
|}.

Lemma rename_result_of_option (T : nominalType) :
  equivariant (@result_of_option T).
Proof. by move=> pm [v|]. Qed.

Lemma result_of_optionD (T : nominalType) o (x : T) :
  result_of_option o = Done x <->
  o = Some x.
Proof. case: o=> [?|] //=; split; congruence. Qed.

Lemma rename_bound_sem pm s c k :
  rename pm (eval_com bound_sem s c k) =
  eval_com bound_sem (rename pm s) c k.
Proof.
elim: k s c=> [//=|k IH] s c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- by rewrite renamerE rename_bound_assn.
- by rewrite rename_result_of_option rename_bound_load.
- by rewrite rename_result_of_option rename_bound_store.
- by rewrite rename_result_of_option rename_bound_alloc.
- by rewrite rename_result_of_option rename_bound_free.
- by [].
- rewrite -IH; case: eval_com=> // s' /=.
  by rewrite IH.
- rewrite -rename_bound_eval_cond.
  by case: bound_eval_cond => [[|]|] //=.
- rewrite -rename_bound_eval_cond.
  by case: bound_eval_cond => [[|]|] //=.
Qed.

Lemma bound_eval_com_domm s s' c k :
  fsubset (vars_c c) (vars_s s) ->
  eval_com bound_sem s c k = Done s' ->
  vars_s s' = vars_s s.
Proof.
elim: k s s' c => [|k IH] /= s s'; first by [].
case: s / boundP=> /= [A [ls h] subs].
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] /=.
- rewrite fsubU1set !vars_sE=> /andP [Px Pe] [<-].
  rewrite bound_assnE /= !vars_sE domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- rewrite bound_loadE /=.
  case: eval_expr => // p; case: (h p)=> [v|] //=.
  rewrite fsubU1set !vars_sE=> /andP [Px Pe] [<-]; rewrite !vars_sE domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- rewrite bound_storeE !vars_sE /=.
  case: eval_expr => // p; rewrite /updm; case: (h p)=> [v|] //=.
  by rewrite fsubUset=> /andP [Pe Pe'] [<-]; rewrite vars_sE.
- admit.
  (*case: eval_expr => // - [n|] //.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.*)
- rewrite bound_freeE vars_sE /=; case: eval_expr => // p.
  have [|]:= altP eqP=> // _; case: free_fun=> // h'' _ [<-].
  by rewrite vars_sE.
- congruence.
- move=> sub; rewrite vars_sE; case eval_c1: (eval_com _ _ _) => [s''| | ] //.
  move: sub; rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  move: (IH _ _ _ vars_c1 eval_c1); rewrite vars_sE=> e.
  rewrite vars_sE -e in vars_c2.
  by rewrite (IH _ _ _ vars_c2 eval_c2).
- rewrite bound_eval_condE; case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
rewrite bound_eval_condE; case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Lemma frame_ok s1 s1' s2 c k :
  fsubset (vars_c c) (vars_s s1) ->
  fdisjoint (objs s1) (objs s2) ->
  eval_com bound_sem s1 c k = Done s1' ->
  eval_com bound_sem (s1 * s2) c k = Done (s1' * s2).
Proof.
elim: k s1 s1' c => [|k IH] //= s1 s1'.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- by move=> sub _ [<-]; rewrite bound_assn_frame.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/bound_load_frame_ok.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/bound_store_frame_ok.
- move=> sub _ /result_of_optionD ?.
  by apply/result_of_optionD/bound_alloc_ok.
- move=> sub dis /result_of_optionD ?.
  by apply/result_of_optionD/bound_free_ok.
- by move=> _ _ [<-].
- rewrite fsubUset=> /andP [sub1 sub2] dis.
  case eval_c1: eval_com=> [s1''| |] //=.
  rewrite (IH _ _ _ sub1 dis eval_c1).
  have sub2': fsubset (vars_c c2) (vars_s s1'').
    by rewrite (bound_eval_com_domm sub1 eval_c1).
  apply/(IH _ _ _ sub2').
  admit.
- rewrite !fsubUset -andbA=> /and3P [sub_e sub1 sub2] dis.
  case eval_

Lemma eval_com_domm safe ls h ls' h' c k :
  fsubset (vars_c c) (domm ls) ->
  eval_com (basic_sem safe) (ls, h) c k = Done (ls', h') ->
  domm ls' = domm ls.
Proof.
elim: k ls ls' h h' c => [|k IH] //= ls ls' h h'.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- case: eval_expr => // p; case: (h p)=> [v|] //=.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- case: eval_expr => // p; rewrite /updm; case: (h p)=> [v|] //=.
  by rewrite fsubUset=> /andP [Pe Pe'] [<- _].
- case: eval_expr => // - [n|] //.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- case: eval_expr => // p.
  by have [|]:= altP eqP=> // _; case: free_fun=> // h'' _ [<- _].
- congruence.
- case eval_c1: eval_com=> [[ls'' h'']| | ] //.
  rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  rewrite -(IH _ _ _ _ _ vars_c1 eval_c1) in vars_c2 *.
  by rewrite (IH _ _ _ _ _ vars_c2 eval_c2).
- case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Theorem frame_ok ls1 h1 ls2 h2 ls1' h1' c k :
  fsubset (vars_c c) (domm ls1) ->
  eval_com (basic_sem true) (ls1, h1) c k = Done (ls1', h1') ->
  fdisjoint (domm ls1) (domm ls2) ->
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  exists2 pm,
    eval_com (basic_sem true) (unionm ls1 ls2, unionm h1 h2) c k =
    Done (unionm (rename pm ls1') ls2,
          unionm (rename pm h1') h2) &
    fdisjoint (names (domm (rename pm h1'))) (names (domm h2)) &&
    fsubset (names (rename pm ls1', rename pm h1') :&: names (ls2, h2))
            (names (ls1, h1)).
Proof.
elim: k ls1 ls1' h1 h1' c => [//=|k IH] ls1 ls1' h1 h1' c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c].
- (* Assn *)
  rewrite fsubU1set=> /andP [Px Pe] /= [<- <-] dis_l dis_h.
  exists 1; rewrite !rename1 // ?setm_union ?(eval_expr_unionm _ _ Pe) //.
  rewrite dis_h /= fsubIset //; apply/orP; left; rewrite fsetSU //=.
  rewrite (fsubset_trans (namesm_set ls1 x _)) // 2!fsubUset fsubsetxx.
  by rewrite fsub0set eval_expr_names.
- (* Load *)
  rewrite fsubU1set=> /andP [Px Pe] /= eval_c dis_l dis_h.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  case get_p: (h1 p)=> [v|] // [<- <-].
  exists 1; rewrite !rename1.
    by rewrite ?eval_expr_unionm // ?eval_e ?unionmE ?get_p /= setm_union.
  rewrite dis_h /= fsubIset //; apply/orP; left.
  rewrite  // fsubUset /= fsubsetUr andbT.
  rewrite (fsubset_trans (namesm_set ls1 x v)) // -fsetUA fsetUS //=.
  rewrite fsubUset fsub0set /=; apply/fsubsetP=> i Pi.
  by apply/namesmP; eapply PMFreeNamesVal; eauto.
- (* Store *)
  rewrite fsubUset=> /andP [Pe Pe'] /= eval_c dis_l dis_h.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  rewrite /updm.
  case get_p: (h1 p)=> [v|] //= [<- <-].
  exists 1; rewrite !rename1.
    rewrite eval_expr_unionm // eval_e unionmE get_p /=.
    by rewrite setm_union eval_expr_unionm //.
  apply/andP; split.
    rewrite domm_set (_ : p |: domm h1 = domm h1) //.
    apply/eq_fset=> p'; rewrite in_fsetU1.
    by have [->|//] := altP eqP; rewrite mem_domm get_p.
  apply/fsubIset/orP; left; rewrite // fsubUset fsubsetUl /=.
  rewrite (fsubset_trans (namesm_set h1 p _)) // -fsetUA fsetUC fsetSU //=.
  rewrite fsubUset eval_expr_names andbT.
  by move: (eval_expr_names true ls1 e); rewrite eval_e.
- (* Alloc *)
  rewrite fsubU1set=> /andP [Px Pe] /=.
  case eval_e: eval_expr=> [ | [n|] | |] // [<- <-] dis_l dis_h.
  rewrite /alloc_fun -!lock /=.
  set i := fresh (names (ls1, h1)).
  set i' := fresh (names (unionm ls1 ls2, unionm h1 h2)).
  set pm := fperm2 i i'.
  have Fi := freshP _ : i \notin names (ls1, h1).
  have Fi' := freshP _ : i' \notin names (unionm ls1 ls2, unionm h1 h2).
  have re_h1 : rename pm (init_block h1 i n) = init_block h1 i' n.
    rewrite /init_block renamem_union.
    congr unionm.
      rewrite renamem_mkpartmapf.
      congr mkpartmapf; rewrite renamesE -[in LHS]map_comp /=.
      by apply/eq_map=> n' /=; rewrite renamepE /= renamenE fperm2L.
    rewrite names_disjointE // supp_fperm2.
    case: ifP=> _; first by rewrite /fdisjoint fset0I.
    apply/fdisjointP=> i'' /fset2P [->|->] {i''}.
      by apply: contra Fi=> Pi; apply/fsetUP; right=> /=.
    apply: contra Fi'=> Pi'; apply/fsetUP; right=> /=.
    apply/namesmP; case/namesmP: Pi'=> p v Pp Pi'.
      eapply PMFreeNamesKey; eauto.
      by rewrite unionmE Pp.
    suff h : unionm h1 h2 p = Some v by eapply PMFreeNamesVal; eauto.
    by rewrite unionmE Pp.
  exists pm.
    rewrite eval_expr_unionm // eval_e -!lock /= renamem_set.
    rewrite renamevE renamepE /= renamenE fperm2L setm_union.
    rewrite re_h1 init_block_unionm; congr Done; congr pair.
    congr unionm; apply/eq_partmap=> x'; rewrite 2!setmE renamemE fperm2V.
    have [//|_] := altP eqP.
    case get_x': (ls1 x')=> [v|] //; rewrite renameoE /= names_disjointE //.
    rewrite supp_fperm2; case: ifP=> _; first by rewrite /fdisjoint fset0I.
    apply/fdisjointP=> i'' /fset2P [->|->] {i''}.
      apply: contra Fi=> Pi; apply/fsetUP; left=> /=.
      by apply/namesmP; eapply PMFreeNamesVal; eauto.
    apply: contra Fi'=> Pi'; apply/fsetUP; left=> /=.
    have ? : unionm ls1 ls2 x' = Some v by rewrite unionmE get_x'.
    by apply/namesmP; eapply PMFreeNamesVal; eauto.
  rewrite re_h1; apply/andP; split.
    have: fsubset (names (domm (init_block h1 i' n))) (i' |: names (domm h1)).
      rewrite /init_block domm_union namesfsU.
      apply/fsubsetP=> i'' /fsetUP [/namesfsP [p /dommP [v Pv] Pi'']|].
        move: Pv; rewrite mkpartmapfE.
        case: ifP Pi''=> // /mapP [off Poff ->]; rewrite in_fsetU in_fset0 orbF.
        by move=> /= /namesnP <- _; rewrite in_fsetU1 eqxx.
      by move=> h; rewrite in_fsetU1 orbC h.
    move=> /fsubsetP sub; apply/fdisjointP=> i'' /sub /fsetU1P [->{i''}|].
      apply: contra Fi'=> Pi'; apply/fsetUP; right=> /=; apply/namesmP.
      rewrite fdisjointC in dis_h; move/fdisjointP/(_ _ Pi') in dis_h.
      case/namesfsP: Pi'=> [p /dommP [v Pv] Pi'].
      have ?: unionm h1 h2 p = Some v.
        rewrite unionmE; case get_h1: (h1 p) => [v'|] //=.
        suff : ~~ true by [].
        apply: contra dis_h=> _; apply/namesfsP; exists p=>//.
        by apply/dommP; eauto.
      by eapply PMFreeNamesKey; eauto.
    by move: i''; apply/fdisjointP.
  rewrite fsetIUl  /= fsetUSS //.
    rewrite renamem_set renamevE renamepE /= renamenE fperm2L.
    rewrite (fsubset_trans (fsetSI _ (namesm_set _ _ _))) //.
    rewrite 2!fsetIUl fset0I fsetU0 namesvE /= names_disjointE.
      rewrite fsubUset fsubsetIl /=.
      rewrite (_ : _ :&: _ = fset0) ?fsub0set //.
      apply/eqP/fdisjointP=> ? /fset1P ->.
      apply: contra Fi'; rewrite in_fsetU /= => Pi'.
      rewrite in_fsetU /= namesm_union_disjoint //.
      rewrite namesm_union_disjoint // ?fdisjoint_names_domm //.
      rewrite in_fsetU orbC in_fsetU.
      by case/orP: Pi'=> [->|->]; rewrite !orbT.
    rewrite supp_fperm2; case: ifP => _; first by rewrite /fdisjoint fset0I.
    apply/fdisjointP=> i'' /fset2P [->|->] {i''}.
      by apply: contra Fi; rewrite (in_fsetU _ (names ls1)) => ->.
    apply: contra Fi'=> Pi'; apply/fsetUP; left.
    case/namesmP: Pi'=> [x' v //|x' v Px' Pi'].
    have ?: unionm ls1 ls2 x' = Some v by rewrite unionmE Px'.
    by apply/namesmP=> /=; eapply PMFreeNamesVal; eauto.
  rewrite (fsubset_trans (fsetSI _ (names_init_block _ _ _))) //.
  rewrite fsetU1E fsetIUl fsubUset fsubsetIl andbT.
  apply/fsubsetP=> i'' /fsetIP [/fset1P -> {i''}].
  move=> Pi'; move: Fi'; rewrite in_fsetU /=.
  rewrite (namesm_union_disjoint dis_l).
  rewrite (namesm_union_disjoint (fdisjoint_names_domm dis_h)) negb_or.
  rewrite in_fsetU negb_or.
  rewrite in_fsetU in Pi'; case/orP: Pi'.
    by move=> /= ->; rewrite andbF.
  by move=> /= Pi' /andP [_]; rewrite in_fsetU Pi' orbT.
- (* Free *)
  move=> /= sub; rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p|] //=.
  have [|] := altP eqP=> // _.
  case free_p: free_fun=> [h'|] // [<- <-] // dis_l dis_h.
  have dis': fdisjoint (domm h1) (domm h2).
    apply/fdisjointP=> p' Pp'.
    have {Pp'} Pp': p'.1 \in names (domm h1).
      apply/namesfsP; exists p'=> //.
      by rewrite in_fsetU; apply/orP; left; apply/namesnP.
    move: (fdisjointP _ _ dis_h _ Pp'); apply: contra=> {Pp'} Pp'.
    by apply/namesfsP; exists p'=> //; apply/namesnP.
  move: free_p; rewrite /free_fun -!lock.
  rewrite !mem_domm_curry domm_union imfsetU in_fsetU /=.

  case: fpickP=> [p' /eqP Pp' /dommP [v Pv]|] //= [eh'].
  exists 1; rewrite !rename1.
    rewrite -eh'.
    case: fpickP=> [p'' /eqP Pp'' /dommP [v' Pv']|] /=.
      rewrite filterm_union //; congr Done; congr pair; congr unionm.
      apply/eq_partmap=> p'''; rewrite filtermE.
      case get_p''': (h2 _) => [v''|] //=.
      have [Pe|] //= := altP eqP.
      have: p'.1 \in names (domm h1).
        apply/namesfsP; exists p'; last by apply/namesnP.
        by apply/dommP; eauto.
      move=> /(fdisjointP _ _ dis_h _); rewrite {}Pp' -{}Pe=> Pp'''.
      apply/eqP; apply: contra Pp'''=> _; apply/namesfsP.
      exists p'''; last by apply/namesnP.
      by apply/dommP; eauto.
    move=> /(_ p'); rewrite mem_domm unionmE Pv => /(_ erefl).
    by rewrite Pp' eqxx.
  subst h'; rewrite /fdisjoint -fsubset0; apply/andP; split.
    rewrite (fsubset_trans (fsetSI _ (namesfs_subset (domm_filter _ h1)))) //.
    by rewrite fsubset0.
  rewrite fsetIUl fsetUSS //= ?fsubsetIl //.
  rewrite (fsubset_trans (fsetSI _ (namesm_filter _ h1))) //.
  by rewrite fsubsetIl.
- (* Skip *)
  by move=> _ [<- <-] dis_l dis_h; exists 1;
  rewrite !rename1 // dis_h fsubsetIl.
- (* Seq *)
  rewrite /= fsubUset=> /andP [sub1 sub2].
  case eval_c1: eval_com=> [[ls' h']| |] //= eval_c2 dis_l dis_h.
  have [pm eval_c1' /andP [dis' sub']] :=
    IH _ _ _ _ _ sub1 eval_c1 dis_l dis_h.
  have [pm' eval_c2'] := renaming ls' h' c2 k pm.
  rewrite eval_c2 renamerE in eval_c2'.
  rewrite -(eval_com_domm sub1 eval_c1)
           (_ : domm ls' = domm (rename pm ls')) in sub2; last first.
    by rewrite -renamem_dom renamefsE -{1}(imfset_id (domm ls')).
  have [|pm'' eval_c2'' /andP [dis'' sub'']] :=
    IH _ _ _ _ _ sub2 eval_c2' _ dis'.
    rewrite -renamem_dom (eval_com_domm sub1 eval_c1) renamefsE.
    by rewrite (eq_imfset (_ : rename pm =1 id)) ?imfset_id //.
  exists (pm'' * pm'); rewrite -!renameD // ?eval_c1' //.
  apply/andP; split=> //; rewrite (fsubset_trans _ sub') // fsubsetI.
  by rewrite sub'' fsubsetIr.
- (* If *)
  rewrite /= 2!fsubUset -andbA=> /and3P [sub_e sub_1 sub_2].
  case eval_e: eval_expr=> [b| | |] //=.
  have {sub_1 sub_2} sub_c: fsubset (vars_c (if b then c1 else c2)) (domm ls1).
    by case: b eval_e.
  move=> eval_c dis_l dis_h.
  have [pm eval_c' eval_e'] := IH _ _ _ _ _ sub_c eval_c dis_l dis_h.
  by exists pm; rewrite // eval_expr_unionm // eval_e.
(* While *)
rewrite /= fsubUset=> /andP [sub_e sub_c].
case eval_e: eval_expr=> [b| | |] //=.
set c' := if b then Seq c (While e c) else Skip.
have sub_c' : fsubset (vars_c c') (domm ls1).
  rewrite /c' /=; case: (b)=> //; rewrite ?fsub0set //.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub_e sub_c.
move=> eval_c' dis_l dis_h.
have [pm eval_c'' dis'] := IH _ _ _ _ _ sub_c' eval_c' dis_l dis_h.
by exists pm; rewrite // eval_expr_unionm // eval_e.
Qed.

Theorem frame_loop ls1 h1 ls2 h2 c k :
  fsubset (vars_c c) (domm ls1) ->
  eval_com (basic_sem true) (ls1, h1) c k = NotYet ->
  fdisjoint (domm ls1) (domm ls2) ->
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  eval_com (basic_sem true) (unionm ls1 ls2, unionm h1 h2) c k = NotYet.
Proof.
elim: k ls1 h1 c => [//=|k IH] ls1 h1 c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //.
- (* Load *)
  rewrite fsubU1set=> /andP [Px Pe] /= eval_c dis_l dis_h.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  by case get_p: (h1 p)=> [v|] //.
- (* Store *)
  rewrite fsubUset=> /andP [Pe Pe'] /= eval_c dis_l dis_h.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  by rewrite /updm; case get_p: (h1 p)=> [v|] //=.
- (* Alloc *)
  rewrite fsubU1set=> /andP [Px Pe] /=.
  by case eval_e: eval_expr=> [ | [n|] | |].
- (* Free *)
  move=> /= sub; case eval_e: eval_expr=> [| |p|] //=.
  have [|] := altP eqP => // _.
  by case free_p: free_fun=> [h'|].
- (* Seq *)
  rewrite /= fsubUset=> /andP [sub1 sub2].
  case eval_c1: eval_com=> [[ls' h']| |] //= eval_c2 dis_l dis_h;
    last by rewrite IH.
  have [pm eval_c1' /andP [dis' _]] := frame_ok sub1 eval_c1 dis_l dis_h.
  rewrite eval_c1' IH; eauto.
  - rewrite -renamem_dom renamefsE (eq_imfset (_ : rename pm =1 id)) //.
    by rewrite imfset_id (eval_com_domm sub1 eval_c1).
  - have [pm' ->] := renaming ls' h' c2 k pm.
    by rewrite eval_c2.
  rewrite -renamem_dom (eval_com_domm sub1 eval_c1) renamefsE.
  by rewrite (eq_imfset (_ : rename pm =1 id)) ?imfset_id //.
- (* If *)
  rewrite /= 2!fsubUset -andbA=> /and3P [sub_e sub_1 sub_2].
  case eval_e: eval_expr=> [b| | |] //=.
  have {sub_1 sub_2} sub_c: fsubset (vars_c (if b then c1 else c2)) (domm ls1).
    by case: b eval_e.
  by move=> eval_c dis_l dis_h; rewrite eval_expr_unionm // eval_e IH.
(* While *)
rewrite /= fsubUset=> /andP [sub_e sub_c].
case eval_e: eval_expr=> [b| | |] //=.
set c' := if b then Seq c (While e c) else Skip.
have sub_c' : fsubset (vars_c c') (domm ls1).
  rewrite /c' /=; case: (b)=> //; rewrite ?fsub0set //.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub_e sub_c.
by move=> eval_c' dis_l dis_h; rewrite eval_expr_unionm // eval_e IH.
Qed.

Theorem frame_error ls1 h1 ls2 h2 c k :
  fsubset (vars_c c) (domm ls1) ->
  eval_com (basic_sem true) (ls1, h1) c k = Error ->
  fdisjoint (domm ls1) (domm ls2) ->
  fdisjoint (names (ls1, h1)) (names (domm h2)) ->
  eval_com (basic_sem true) (unionm ls1 ls2, unionm h1 h2) c k = Error.
Proof.
move=> sub eval_c disl' dis.
have [disl dish] : fdisjoint (names ls1) (names (domm h2)) /\
                   fdisjoint (names h1) (names (domm h2)).
  by move: dis; rewrite /fdisjoint fsetIUl /= fsetU_eq0=> /andP []; eauto.
elim: k ls1 h1 c sub eval_c disl' disl dish {dis} => [//=|k IH] ls1 h1 c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //.
- (* Load *)
  rewrite fsubU1set=> /andP [Px Pe] /= eval_c disl' /fdisjointP disl dish.
  rewrite eval_expr_unionm //.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  rewrite unionmE; case get_p: (h1 p)=> [v|] //= _.
  case get_p': (h2 p) => [v|] //.
  move: (eval_expr_names true ls1 e); rewrite eval_e namesvE fsub1set.
  move=> /disl c; apply/eqP; apply: contraNT c=> _; apply/namesfsP; exists p.
    by rewrite mem_domm get_p'.
  by apply/fsetUP; left; apply/namesnP.
- (* Store *)
  rewrite fsubUset=> /andP [Pe Pe'] /= eval_c disl' /fdisjointP disl dish.
  rewrite eval_expr_unionm //.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  rewrite eval_expr_unionm // /updm unionmE.
  case get_p: (h1 p)=> [v|] //= _.
  case get_p': (h2 p)=> [v|] //=.
  move: (eval_expr_names true ls1 e); rewrite eval_e namesvE fsub1set.
  move=> /disl c; apply/eqP; apply: contraNT c=> _; apply/namesfsP; exists p.
    by rewrite mem_domm get_p'.
  by apply/fsetUP; left; apply/namesnP.
- (* Alloc *)
  rewrite fsubU1set=> /andP [Px Pe] /=.
  rewrite eval_expr_unionm //.
  by case eval_e: eval_expr=> [ | [n|] | |] //.
- (* Free *)
  move=> /= sub; rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p|] //=.
  have [|] := altP eqP=> // _.
  case free_p: free_fun=> [h'|] // _ disl' /fdisjointP disl dish.
  have dis': fdisjoint (domm h1) (domm h2).
    apply/fdisjointP=> p' Pp'.
    have {Pp'} Pp': p'.1 \in names (domm h1).
      apply/namesfsP; exists p'=> //.
      by rewrite in_fsetU; apply/orP; left; apply/namesnP.
    have {Pp'} Pp': p'.1 \in names h1 by rewrite namesmE in_fsetU Pp'.
    move: (fdisjointP _ _ dish _ Pp'); apply: contra=> {Pp'} Pp'.
    by apply/namesfsP; exists p'=> //; apply/namesnP.
  move: free_p; rewrite /free_fun -!lock.
  case: fpickP=> [p' /eqP Pp' /dommP [v Pv]|] //= Pp _.
  case: fpickP=> [p'' /eqP Pp'' /dommP [v']|] //=.
  rewrite unionmE; case get_p': (h1 p'') => [v''|] //=.
    move=> _ {v'}.
    suff /Pp: p'' \in domm h1 by rewrite Pp'' eqxx.
    by rewrite mem_domm get_p'.
  move: (eval_expr_names true ls1 e); rewrite eval_e namesvE fsub1set => /disl.
  move=> c get_p''.
  apply/eqP; apply: contraNT c => _; rewrite -Pp''.
  apply/namesfsP; exists p''; first by rewrite mem_domm get_p''.
  by apply/namesnP.
- (* Seq *)
  rewrite /= fsubUset=> /andP [sub1 sub2] eval_c disl' disl dish.
  have dish': fdisjoint (names (domm h1)) (names (domm h2)).
    by move: dish; rewrite /fdisjoint namesmE fsetIUl fsetU_eq0=> /andP [].
  case eval_c1: eval_com eval_c=> [[ls' h']| |] //= eval_c2;
    last by rewrite IH.
  have [pm eval_c1' /andP [dis' sub]] := frame_ok sub1 eval_c1 disl' dish'.
  rewrite eval_c1'.
  have [pm' eval_c2'] := renaming ls' h' c2 k pm.
  rewrite eval_c2 renamerE in eval_c2'.
  have dis: names (ls1, h1) :&: names (domm h2) = fset0.
    by rewrite fsetIUl /= (eqP disl) (eqP dish) fsetU0.
  have: fdisjoint (names (rename pm ls', rename pm h')) (names (domm h2)).
    rewrite /fdisjoint -fsubset0 -dis fsubsetI fsubsetIr andbT.
    rewrite (fsubset_trans _ sub) // fsetIS // fsubsetU //=.
    by rewrite fsubsetUl orbT.
  rewrite /fdisjoint fsetIUl /= fsetU_eq0=> /andP [??].
  rewrite IH //.
    rewrite -renamem_dom renamefsE (eq_imfset (_ : rename pm =1 id)) //.
    by rewrite imfset_id (eval_com_domm sub1 eval_c1).
  rewrite -renamem_dom (eval_com_domm sub1 eval_c1) renamefsE.
  by rewrite (eq_imfset (_ : rename pm =1 id)) ?imfset_id //.
- (* If *)
  rewrite /= 2!fsubUset -andbA=> /and3P [sub_e sub_1 sub_2].
  rewrite eval_expr_unionm //; case eval_e: eval_expr=> [b| | |] //=.
  have {sub_1 sub_2} sub_c: fsubset (vars_c (if b then c1 else c2)) (domm ls1).
    by case: b eval_e.
  by move=> eval_c disl' disl dish; rewrite IH.
(* While *)
rewrite /= fsubUset=> /andP [sub_e sub_c].
rewrite eval_expr_unionm //; case eval_e: eval_expr=> [b| | |] //=.
set c' := if b then Seq c (While e c) else Skip.
have sub_c' : fsubset (vars_c c') (domm ls1).
  rewrite /c' /=; case: (b)=> //; rewrite ?fsub0set //.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub_e sub_c.
by move=> eval_c' disl' disl dish; rewrite IH.
Qed.

Corollary noninterference ls1 h1 ls21 h21 ls' h' ls22 h22 c k :
  fsubset (vars_c c) (domm ls1) ->
  fdisjoint (domm ls1) (domm ls21) ->
  fdisjoint (names (ls1, h1)) (names (domm h21)) ->
  fdisjoint (domm ls1) (domm ls22) ->
  fdisjoint (names (ls1, h1)) (names (domm h22)) ->
  eval_com (basic_sem true) (unionm ls1 ls21, unionm h1 h21) c k =
  Done (ls', h') ->
  exists ls1' h1' pm1 pm2,
    [/\ eval_com (basic_sem true) (ls1, h1) c k = Done (ls1', h1'),
        ls' = unionm (rename pm1 ls1') ls21,
        h' = unionm (rename pm1 h1') h21 &
        eval_com (basic_sem true) (unionm ls1 ls22, unionm h1 h22) c k =
        Done (unionm (rename pm2 ls1') ls22,
              unionm (rename pm2 h1') h22)].
Proof.
move=> sub disl1 dis1 disl2 dis2 eval_c.
have dis1' : fdisjoint (names (domm h1)) (names (domm h21)).
  rewrite /fdisjoint fsetIUl -fsubset0 fsubUset/= in dis1.
  case/andP: dis1=> [_ dis1].
  rewrite fsetIUl fsubUset in dis1; case/andP: dis1=> [dis1 _].
  by rewrite /fdisjoint -fsubset0.
have dis2' : fdisjoint (names (domm h1)) (names (domm h22)).
  rewrite /fdisjoint fsetIUl -fsubset0 fsubUset/= in dis2.
  case/andP: dis2=> [_ dis2].
  rewrite fsetIUl fsubUset in dis2; case/andP: dis2=> [dis2 _].
  by rewrite /fdisjoint -fsubset0.
case eval_c': (eval_com _ (ls1, h1) c k) => [[ls1' h1']| |].
- exists ls1', h1'.
  have [pm1 eval_c1 _] := frame_ok sub eval_c' disl1 dis1'.
  move: eval_c; rewrite eval_c1=> - [<- <-].
  have [pm2 eval_c2 _] := frame_ok sub eval_c' disl2 dis2'.
  by exists pm1, pm2; split; eauto.
- have eval_c'' := frame_error sub eval_c' disl1 dis1.
  by rewrite eval_c'' in eval_c.
have eval_c'' := frame_loop sub eval_c' disl1 dis1'.
by rewrite eval_c'' in eval_c.
Qed.

Lemma eval_com_domm safe ls h ls' h' c k :
  fsubset (vars_c c) (domm ls) ->
  eval_com (basic_sem safe) (ls, h) c k = Done (ls', h') ->
  domm ls' = domm ls.
Proof.
elim: k ls ls' h h' c => [|k IH] //= ls ls' h h'.
case=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- case: eval_expr => // p; case: (h p)=> [v|] //=.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- case: eval_expr => // p; rewrite /updm; case: (h p)=> [v|] //=.
  by rewrite fsubUset=> /andP [Pe Pe'] [<- _].
- case: eval_expr => // - [n|] //.
  rewrite fsubU1set=> /andP [Px Pe] [<- _]; rewrite domm_set.
  apply/eqP; rewrite eqEfsubset; apply/andP; split.
    by rewrite fsubU1set Px fsubsetxx.
  by rewrite fsetU1E fsubsetUr.
- case: eval_expr => // p.
  by have [|]:= altP eqP=> // _; case: free_fun=> // h'' _ [<- _].
- congruence.
- case eval_c1: eval_com=> [[ls'' h'']| | ] //.
  rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  rewrite -(IH _ _ _ _ _ vars_c1 eval_c1) in vars_c2 *.
  by rewrite (IH _ _ _ _ _ vars_c2 eval_c2).
- case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Theorem weak_frame ls1 h1 ls2 h2 ls' h' safe c k :
  fsubset (vars_c c) (domm ls1) ->
  fdisjoint (domm ls1) (domm ls2) ->
  fdisjoint (names (ls1, h1)) (names (domm h2)) ->
  eval_com (basic_sem safe) (unionm ls1 ls2, unionm h1 h2) c k =
  Done (ls', h') ->
  exists ls1' h1',
    [/\ ls' = unionm ls1' ls2,
        h'  = unionm h1' h2,
        fdisjoint (domm ls1') (domm ls2) &
        fsubset (names (ls1', h1') :&: (names h2))
                (names (ls1, h1))].
Proof.
elim: k ls1 h1 ls' h' c=> [//=|k IH] ls1 h1 ls' h' c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //=.
- (* Assn *)
  rewrite fsubU1set=> /andP [Px sub] disl dish [<- <-].
  rewrite setm_union; do 3!eexists; eauto.
    by rewrite domm_set; apply/fdisjointP=> x' /fsetU1P [->|];
    move/fdisjointP: disl; apply.
  rewrite fsetIUl fsetUSS //= 1?fsubsetIl //.
  rewrite (fsubset_trans (fsetSI _ (namesm_set _ _ _))) // fsetU0.
  rewrite eval_expr_unionm // fsetIUl fsubUset fsubsetIl /=.
  rewrite (fsubset_trans (fsubsetIl _ _)) //.
  by rewrite (fsubset_trans (eval_expr_names _ _ _)) // fsubsetxx.
- (* Load *)
  rewrite fsubU1set=> /andP [Px sub] disl dish.
  rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p|] //.
  rewrite unionmE; case get_p: (h1 p)=> [v|] /=.
    move=> [<- <-]; rewrite setm_union; do 3!eexists; eauto.
      by rewrite domm_set; apply/fdisjointP=> x' /fsetU1P [->|];
      move/fdisjointP: disl; apply.
    rewrite fsetIUl /= fsubUset; apply/andP; split.
      apply: (fsubset_trans (fsubsetIl _ _)).
      apply: (fsubset_trans (namesm_set _ _ _)).
      rewrite fsetU0 fsetUSS // ?fsubsetxx //=.
      apply/fsubsetP=> n Pn; apply/namesmP.
      by eapply PMFreeNamesVal; eauto.
    by apply: fsubIset; rewrite fsubsetUr.
  move: (eval_expr_names safe ls1 e); rewrite eval_e namesvE fsub1set=> Pp.
  move/fdisjointP/(_ p.1): dish; rewrite in_fsetU /= Pp /= => /(_ erefl).
  case get_p': (h2 p) => [v|] //= /namesfsPn/(_ p).
  by rewrite mem_domm get_p'=> /(_ erefl); rewrite in_fsetU in_fset1 eqxx.
- (* Store *)
  rewrite fsubUset=> /andP [sub1 sub2] disl dish.
  rewrite !eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p| ] //.
  rewrite /updm unionmE setm_union.
  case get_p: (h1 p)=> [v|] //=.
    move=> [<- <-]; do 3!eexists; eauto.
    apply: (fsubset_trans (fsubsetIl _ _)).
    rewrite fsubUset; apply/andP; split; first by rewrite fsubsetUl.
    apply/(fsubset_trans (namesm_set _ _ _)); rewrite 2!fsubUset.
    rewrite fsubsetUr /=; apply/andP; split.
      apply/fsubsetU/orP; right; apply/fsubsetP=> i Pi /=.
      by apply/namesmP; eapply PMFreeNamesKey; eauto.
    by apply/(fsubset_trans (eval_expr_names _ _ _))/fsubsetUl.
  move: (eval_expr_names safe ls1 e); rewrite eval_e namesvE fsub1set=> Pp.
  move/fdisjointP/(_ p.1): dish; rewrite in_fsetU /= Pp /= => /(_ erefl).
  case get_p': (h2 p) => [v|] //= /namesfsPn/(_ p).
  by rewrite mem_domm get_p'=> /(_ erefl); rewrite in_fsetU in_fset1 eqxx.
- (* Alloc *)
  rewrite fsubU1set=> /andP [Px sub] disl dish; rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [|[n|]| |] //= [<- <-].
  rewrite setm_union /alloc_fun /= -lock /= init_block_unionm.
  have dis': fdisjoint (domm h1) (domm h2).
    apply/fdisjoint_names_domm/fdisjointP=> i Pi'.
    by move/fdisjointP: dish; apply; apply/fsetUP; right; apply/fsetUP; left.
  have F := (freshP (names (unionm ls1 ls2, unionm h1 h2))).
  do 3!eexists; eauto.
    by rewrite domm_set; apply/fdisjointP=> x' /fsetU1P [->|];
    move/fdisjointP: disl; apply.
  rewrite fsetIUl fsubUset; apply/andP; split=> /=.
    apply/(fsubset_trans _ (fsubsetUl _ _)).
    apply/(fsubset_trans (fsetSI _ (namesm_set _ _ _))).
    rewrite /= 2!fsetIUl 2!fsubUset fsubsetIl fset0I fsub0set /=.
    apply/fsubsetP=> i /fsetIP [/namesnP -> {i} /= Pi].
    move: F; rewrite in_fsetU negb_or=> /andP [_] /=.
    by rewrite namesm_union_disjoint // in_fsetU negb_or Pi andbF.
  apply/fsubsetU/orP; right.
  apply/(fsubset_trans (fsetSI _ (names_init_block _ _ _)))/fsubsetP.
  move=> i /fsetIP [/fsetU1P [->|//] I].
  move: F; rewrite in_fsetU negb_or /= => /andP [_].
  by rewrite namesm_union_disjoint // in_fsetU I orbT.
- (* Free *)
  move=> sub disl dish; rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [| |p|] //=.
  have [|] := altP eqP=> // _.
  rewrite /free_fun -lock; case: fpickP=> [p' /eqP Pp|] //=.
  rewrite mem_domm unionmE.
  have dish': fdisjoint (names (domm h1)) (names (domm h2)).
    apply/fdisjointP=> i Pi'.
    by move/fdisjointP: dish; apply; apply/fsetUP; right; apply/fsetUP; left.
  case get_p': (h1 p') => [v|] /=.
    move=> _ [<- <-]; exists ls1, (filterm (fun p'' _ => p''.1 != p.1) h1).
    split=> //.
      rewrite filterm_union; last by apply fdisjoint_names_domm.
      congr unionm; apply/eq_partmap=> p''; rewrite filtermE.
      case get_p'': (h2 p'')=> [v'|] //=.
      have [Pp'|] //= := altP eqP.
      have names_p: p.1 \in names (domm h1).
        apply/namesfsP; exists p'; first by rewrite mem_domm get_p'.
        by rewrite -Pp; rewrite in_fsetU; apply/orP; left; apply/namesnP.
      move/fdisjointP: dish'=> /(_ _ names_p).
      suff ->: p.1 \in names (domm h2) by [].
      apply/namesfsP; exists p''; first by rewrite mem_domm get_p''.
      by rewrite -Pp'; rewrite in_fsetU; apply/orP; left; apply/namesnP.
    rewrite fsetIUl fsetUSS //= ?fsubsetIl //.
    by apply/(fsubset_trans (fsubsetIl _ _))/namesm_filter.
  case get_p'': (h2 p') => [v'|] //= _.
  move: (eval_expr_names safe ls1 e); rewrite eval_e namesvE.
  move=> /fsubsetP/(_ p.1); rewrite in_fset1 eqxx=> /(_ erefl) Pp'.
  rewrite fdisjointC in dish; move/fdisjointP/(_ p.1): dish.
  have h: p.1 \in names (domm h2).
    apply/namesfsP; exists p'; first by rewrite mem_domm get_p''.
    by rewrite -Pp in_fsetU; apply/orP; left; apply/namesnP.
  by rewrite in_fsetU Pp' /= => /(_ h).
- (* Skip *)
  move=> _ ? ? [<- <-]; do 3!eexists; eauto; exact: fsubsetIl.
- (* Seq *)
  case eval_c1: eval_com=> [[ls'' h'']| |] //=.
  rewrite fsubUset=> /andP [sub1 sub2] disl dish eval_c2.
  have [ls1' [h1' [? ? disl' sub']]] := IH _ _ _ _ _ sub1 disl dish eval_c1.
  subst ls'' h''.
  have dish': fdisjoint (names (ls1', h1')) (names (domm h2)).
    move/eqP in dish.
    rewrite /fdisjoint -fsubset0 -dish fsubsetI fsubsetIr andbT.
    by rewrite (fsubset_trans _ sub') // fsetIS // fsubsetUl.
  have sub1': fsubset (vars_c c1) (domm (unionm ls1 ls2)).
    by rewrite domm_union (fsubset_trans sub1) // fsubsetUl.
  have sub2' : fsubset (vars_c c2) (domm ls1').
    apply/fsubsetP=> x x_in.
    move/fsubsetP/(_ x x_in): (sub2)=> sub2'.
    have: x \in domm (unionm ls1' ls2).
      by rewrite (eval_com_domm sub1' eval_c1) domm_union in_fsetU sub2'.
    move/fdisjointP/(_ _ sub2') in disl.
    by rewrite domm_union in_fsetU (negbTE disl) orbF.
  have [ls1'' [h1'' [? ? disl'' sub'']]] :=
    IH _ _ _ _ _ sub2' disl' dish' eval_c2.
  subst; do 3!eexists; eauto.
  by apply/(fsubset_trans _ sub'); rewrite fsubsetI fsubsetIr andbT.
- (* If *)
  rewrite 2!fsubUset=> /andP [/andP [sub1 sub2] sub3].
  rewrite eval_expr_unionm //.
  case eval_e: eval_expr=> [b| | |] //= disl dish eval_c.
  have [|ls1' [h1' [? ? disl' sub']]] := IH _ _ _ _ _ _ disl dish eval_c.
    by case: b {eval_e eval_c}.
  by subst ls' h'; do 3!eexists; eauto.
(* While *)
rewrite fsubUset=> /andP [sub1 sub2]; rewrite eval_expr_unionm //.
case eval_e: eval_expr=> [b| | |] //= disl dish eval_c.
have [|ls1' [h1' [? ? sub']]] := IH _ _ _ _ _ _ disl dish eval_c.
  case: (b); last by rewrite fsub0set.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub1.
by subst ls' h'; do 3!eexists; eauto.
Qed.




End Def.
