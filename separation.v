Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg.

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

Definition int_nominalMixin := TrivialNominalMixin int.
Canonical int_nominalType := Eval hnf in NominalType int int_nominalMixin.

Definition string_nominalMixin := TrivialNominalMixin string.
Canonical string_nominalType :=
  Eval hnf in NominalType string string_nominalMixin.

Inductive binop : Type :=
| Add | Mul | Sub | Eq | Leq | And | Or.

Inductive expr :=
| Var of string
| Num of int
| Binop of binop & expr & expr
| ENil.

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

Definition locals := {partmap string -> value}.
Definition heap := {partmap name * int -> value}.

Implicit Types (ls : locals) (h : heap).

Definition init_block h b n :=
  unionm (mkpartmapf (fun _ => VNum 0) [seq (b, Posz i) | i <- iota 0 n]) h.

Definition alloc ls h n :=
  locked (let b := fresh (names (ls, h)) in (b, init_block h b n)).

Definition free h i :=
  locked
  (if fpick (fun p => p.1 == i) (domm h) then
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

Fixpoint eval_expr ls e :=
  match e with
  | Var x => odflt VNil (ls x)
  | Num n => VNum n
  | Binop b e1 e2 => eval_binop b (eval_expr ls e1) (eval_expr ls e2)
  | ENil => VNil
  end.

Inductive result :=
| Done of locals & heap
| Error
| NotYet.

Definition sum_of_result r :=
  match r with
  | Done ls h => inl (ls, h)
  | Error => inr true
  | NotYet => inr false
  end.

Definition result_of_sum r :=
  match r with
  | inl (ls, h) => Done ls h
  | inr true => Error
  | inr false => NotYet
  end.

Lemma sum_of_resultK : cancel sum_of_result result_of_sum.
Proof. by case. Qed.
Lemma result_of_sumK : cancel result_of_sum sum_of_result.
Proof. by do ![case=>//]. Qed.

Definition result_eqMixin := CanEqMixin sum_of_resultK.
Canonical result_eqType := Eval hnf in EqType result result_eqMixin.
Definition result_partOrdMixin := CanPartOrdMixin sum_of_resultK.
Canonical result_partOrdType :=
  Eval hnf in PartOrdType result result_partOrdMixin.
Definition result_ordMixin := CanOrdMixin sum_of_resultK.
Canonical result_ordType := Eval hnf in OrdType result result_ordMixin.
Definition result_nominalMixin := BijNominalMixin sum_of_resultK result_of_sumK.
Canonical result_nominalType :=
  Eval hnf in NominalType result result_nominalMixin.

Fixpoint eval_com ls h c k :=
  if k is S k' then
    match c with
    | Assn x e =>
      Done (setm ls x (eval_expr ls e)) h

    | Load x e =>
      if eval_expr ls e is VPtr p then
        if h p is Some v then Done (setm ls x v) h
        else Error
      else Error

    | Store e e' =>
      if eval_expr ls e is VPtr p then
        if updm h p (eval_expr ls e') is Some h' then Done ls h'
        else Error
      else Error

    | Alloc x e =>
      if eval_expr ls e is VNum (Posz n) then
        let res := alloc ls h n in
        Done (setm ls x (VPtr (res.1, 0 : int))) res.2
      else Error

    | Free e =>
      if eval_expr ls e is VPtr p then
        if free h p.1 is Some h' then
          Done ls h'
        else Error
      else Error

    | Skip => Done ls h

    | Seq c1 c2 =>
      let r1 := eval_com ls h c1 k' in
      if r1 is Done ls' h' then
        eval_com ls' h' c2 k'
      else r1

    | If e ct ce =>
      if eval_expr ls e is VBool b then
        eval_com ls h (if b then ct else ce) k'
      else Error

    | While e c =>
      if eval_expr ls e is VBool b then
        eval_com ls h (if b then Seq c (While e c) else Skip) k'
      else Error
    end
  else NotYet.

Definition refine_result r1 r2 :=
  (r1 == NotYet) || (r1 == r2).

Lemma eval_com_leq ls h c k k' :
  (k <= k')%N ->
  refine_result (eval_com ls h c k) (eval_com ls h c k').
Proof.
move=> Pk; elim: k' k Pk ls h c => [|k' IH] [|k] // /IH {IH} IH ls h.
rewrite /refine_result.
case=> [x e|x e|e e'|x e|e| |c1 c2|e ct ce|e c] /=; try by rewrite eqxx ?orbT.
- case/orP: (IH ls h c1) => [/eqP -> //|/eqP ->].
  case: (eval_com _ _ c1 _) => [ls' h'| |] //=.
  by eauto.
- by case: (eval_expr ls e) => [b| | |] //=; eauto.
by case: (eval_expr ls e) => [b| | |] //=; eauto.
Qed.

Lemma rename_eval_binop pm b v1 v2 :
  rename pm (eval_binop b v1 v2) =
  eval_binop b (rename pm v1) (rename pm v2).
Proof.
case: b v1 v2 => [] [b1|n1|p1|] [b2|n2|p2|] //=.
by rewrite (can_eq (renameK pm)).
Qed.

Lemma rename_eval_expr pm ls e :
  rename pm (eval_expr ls e) =
  eval_expr (rename pm ls) e.
Proof.
elim: e=> [x|n|b e1 IH1 e2 IH2|] //=.
  rewrite renamemE /= [rename _ x]/rename /= /trivial_rename /=.
  by case: (ls x)=> [v|] //=.
by rewrite rename_eval_binop IH1 IH2.
Qed.

Lemma renamerE pm r :
  rename pm r =
  match r with
  | Done ls h => Done (rename pm ls) (rename pm h)
  | Error => Error
  | NotYet => NotYet
  end.
Proof. by case: r. Qed.

Lemma rename_free pm h i :
  rename pm (free h i) = free (rename pm h) (rename pm i).
Proof.
rewrite /free; unlock.
case: fpickP=> [p' /eqP Pp' in_domm'|] //;
case: fpickP=> [p'' /eqP Pp'' in_domm''|] //=; try subst i.
- rewrite renameoE /= renamem_filter; congr Some.
  apply: eq_filterm=> p _ /=.
  by rewrite (can2_eq (renameKV pm) (renameK pm)).
- move=> /(_ (rename pm p')); rewrite domm_rename renamefsE.
  rewrite (mem_imfset_inj _ _ (@rename_inj _ pm)) => /(_ in_domm').
  by rewrite renamepE /= eqxx.
move=> /(_ (rename (pm^-1)%fperm p'')).
rewrite domm_rename renamefsE in in_domm''.
case/imfsetP: in_domm'' => [p' Pp' ?]; subst p''.
rewrite renameK => /(_ Pp').
rewrite renamepE /= in Pp''; move/rename_inj in Pp''; subst i.
by rewrite eqxx.
Qed.

Local Open Scope fset_scope.
Local Open Scope fperm_scope.

Lemma renaming ls h c k pm :
  exists pm',
    eval_com (rename pm ls) (rename pm h) c k =
    rename pm' (eval_com ls h c k).
Proof.
elim: k ls h c pm => [//=|k IH] ls h c pm; first by exists fperm_one.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c].
- by exists pm; rewrite /= renamerE renamem_set rename_eval_expr.
- exists pm=> /=.
  rewrite -rename_eval_expr; case: (eval_expr ls e)=> //= p.
  rewrite renamemE renameK; case Pp: (h p)=> [v|] //=.
  by rewrite renamerE renamem_set.
- exists pm=> /=.
  rewrite -rename_eval_expr; case: (eval_expr ls e)=> //= p.
  rewrite /updm renamemE renameK -rename_eval_expr -renamem_set.
  by case: (h p) => [v|] //= [<- <-] //=.
- rewrite /= -rename_eval_expr.
  case: (eval_expr ls e) => [|[n|]| |]; try by exists pm.
  rewrite renamevE /alloc -2!lock /=.
  set i := fresh (names (ls, h)).
  set i' := fresh (names _).
  set i'' := fresh (supp pm :|: names (ls, h) :|: names (rename pm (ls, h))).
  pose pm' := fperm2 i' i'' * pm * fperm2 i i''; exists pm'.
  have Pi: pm' i = i'.
    do 2![rewrite fpermM /=]; apply: (canLR (fpermKV _)).
    rewrite fperm2V 2!fperm2L; apply/suppPn.
    move: (freshP (supp pm :|: names (ls, h) :|: names (rename pm (ls, h)))).
    by apply: contra=> Pi''; rewrite 3!in_fsetU Pi''.
  have Pj: forall j, j \in names (ls, h) -> pm' j = pm j.
    move=> j Pj {Pi}; rewrite {}/pm'; do 2![rewrite fpermM /=].
    rewrite [in pm _]fperm2D ?fperm2D //.
    + move: (freshP (names (rename pm ls, rename pm h))).
      apply: contra => /eqP; rewrite /i' => <-.
      move: (mem_imfset (rename pm) Pj).
      by rewrite -names_rename.
    + move: (freshP (supp pm :|: names (ls, h) :|: names (rename pm (ls, h)))).
      apply: contra => /eqP; rewrite /i'' => <-.
      rewrite in_fsetU; move: (mem_imfset (rename pm) Pj).
      by rewrite -names_rename renamenE => ->; rewrite orbT.
    + move: (freshP (names (ls, h))).
      by apply: contra => /eqP; rewrite /i => <-.
    move: (freshP (supp pm :|: names (ls, h) :|: names (rename pm (ls, h)))).
    apply: contra => /eqP; rewrite /i'' => <-.
    by rewrite 2!in_fsetU Pj orbT.
  rewrite renamerE renamem_set renamevE renamepE /=; congr Done.
    congr setm.
      by apply: eq_in_rename=> j Pj'; rewrite Pj // in_fsetU /= Pj'.
    by rewrite renamenE Pi.
  apply/eq_partmap=> p; rewrite unionmE 2!renamemE unionmE 2!mkpartmapfE.
  rewrite (_ : [seq (i, Posz n') | n' <- iota 0 n] =
               map (rename pm'^-1) [seq (i', Posz n') | n' <- iota 0 n]).
    rewrite (mem_map (@rename_inj _ _)).
    case: (ifP (p \in _))=> //= _; rewrite -2!renamemE; congr getm; move{p}.
    apply: (@eq_in_rename _ pm pm' h)=> p Pp; rewrite Pj //.
    by rewrite in_fsetU Pp orbT.
  rewrite -[in RHS]map_comp /=; apply: eq_map => n' /=; rewrite renamepE /=.
  by rewrite renamenE -Pi fpermK.
- exists pm; rewrite /eval_com -rename_eval_expr.
  case: (eval_expr ls e) => // p; rewrite renamevE.
  by rewrite renamepE /= -rename_free; case: (free _ _) => [h'|] //=.
- by exists pm.
- have /= [pm' ->] := IH ls h c1 pm.
  case: (eval_com _ _ c1 _)=> [ls' h'| |]; try by exists pm'.
  by have /= [pm'' ->] := IH ls' h' c2 pm'; eauto.
- rewrite /= -rename_eval_expr.
  by case: (eval_expr ls e) => [[]| | |] //=; exists pm.
- rewrite /= -rename_eval_expr.
  by case: (eval_expr ls e) => [[]| | |] //=; exists pm.
Qed.

Fixpoint vars_e e :=
  match e with
  | Var x => fset1 x
  | Num _ => fset0
  | Binop _ e1 e2 => vars_e e1 :|: vars_e e2
  | ENil => fset0
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

Lemma eval_expr_unionm ls1 ls2 e :
  fsubset (vars_e e) (domm ls1) ->
  eval_expr (unionm ls1 ls2) e =
  eval_expr ls1 e.
Proof.
elim: e => [x|n|b e1 IH1 e2 IH2|] //=.
  by rewrite fsub1set unionmE => /dommP [v ->].
by rewrite fsubUset=> /andP [/IH1 {IH1} -> /IH2 {IH2} ->].
Qed.

Lemma eval_com_domm ls h ls' h' c k :
  fsubset (vars_c c) (domm ls) ->
  eval_com ls h c k = Done ls' h' ->
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
- by case: eval_expr => // p; case: free=> // h'' _ [<- _].
- congruence.
- case eval_c1: eval_com=> [ls'' h''| | ] //.
  rewrite fsubUset=> /andP [vars_c1 vars_c2] eval_c2.
  rewrite -(IH _ _ _ _ _ vars_c1 eval_c1) in vars_c2 *.
  by rewrite (IH _ _ _ _ _ vars_c2 eval_c2).
- case: eval_expr=> // - b.
  by rewrite 2!fsubUset -andbA => /and3P [_ vars_c1 vars_c2]; case: b; eauto.
case: eval_expr=> // - [] P; apply: IH.
  by rewrite /= fsetUC -fsetUA fsetUid.
by rewrite fsub0set.
Qed.

Lemma frame_ok ls1 h1 ls2 h2 ls1' h1' c k :
  fsubset (vars_c c) (domm ls1) ->
  eval_com ls1 h1 c k = Done ls1' h1' ->
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  exists2 pm,
    eval_com (unionm ls1 ls2) (unionm h1 h2) c k =
    Done (unionm (rename pm ls1') ls2)
         (unionm (rename pm h1') h2) &
    fdisjoint (names (domm (rename pm h1'))) (names (domm h2)).
Proof.
elim: k ls1 ls1' h1 h1' c => [//=|k IH] ls1 ls1' h1 h1' c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c].
- rewrite fsubU1set=> /andP [Px Pe] /= [<- <-] dis_h.
  by exists 1; rewrite !rename1 // setm_union (eval_expr_unionm _ Pe).
- rewrite fsubU1set=> /andP [Px Pe] /= eval_c dis.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  case get_p: (h1 p)=> [v|] // [<- <-].
  exists 1; rewrite !rename1 // eval_expr_unionm // eval_e unionmE get_p /=.
  by rewrite setm_union.
- rewrite fsubUset=> /andP [Pe Pe'] /= eval_c dis.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  rewrite /updm.
  case get_p: (h1 p)=> [v|] //= [<- <-].
  exists 1; rewrite !rename1.
    rewrite eval_expr_unionm // eval_e unionmE get_p /=.
    by rewrite setm_union eval_expr_unionm //.
  rewrite domm_set (_ : p |: domm h1 = domm h1) //.
  apply/eq_fset=> p'; rewrite in_fsetU1.
  by have [->|//] := altP eqP; rewrite mem_domm get_p.
- rewrite fsubU1set=> /andP [Px Pe] /=.
  case eval_e: eval_expr=> [ | [n|] | |] // [<- <-] dis.
  rewrite /alloc -!lock /=.
  set i := fresh (names (ls1, h1)).
  set i' := fresh (names (unionm ls1 ls2, unionm h1 h2)).
  set pm := fperm2 i i'.
  have re_h1 : rename pm (init_block h1 i n) = init_block h1 i' n.
    rewrite /init_block renamem_union.
    congr unionm.
      rewrite renamem_mkpartmapf.
      congr mkpartmapf; rewrite renamesE -[in LHS]map_comp /=.
      by apply/eq_map=> n' /=; rewrite renamepE /= renamenE fperm2L.
    rewrite names_disjointE // supp_fperm2.
    case: ifP=> _; first by rewrite /fdisjoint fset0I.
    apply/fdisjointP=> i'' /fset2P [->|->] {i''}.
      have := freshP (names (ls1, h1)) : i \notin names (ls1, h1).
      by apply: contra=> Pi; apply/fsetUP; right=> /=.
    have := freshP (names (unionm ls1 ls2, unionm h1 h2))
            : i' \notin names (unionm ls1 ls2, unionm h1 h2).
    apply: contra=> Pi'; apply/fsetUP; right=> /=.
    apply/namesmP; case/namesmP: Pi'=> p v Pp Pi'.
      eapply PMFreeNamesKey; eauto.
      by rewrite unionmE Pp.
    suff h : unionm h1 h2 p = Some v by eapply PMFreeNamesVal; eauto.
    by rewrite unionmE Pp.
  exists pm.
    rewrite eval_expr_unionm // eval_e -!lock /= renamem_set.
    rewrite renamevE renamepE /= renamenE fperm2L setm_union.
    rewrite re_h1 /init_block unionmA; congr Done.
    congr unionm; apply/eq_partmap=> x'; rewrite 2!setmE renamemE fperm2V.
    have [//|_] := altP eqP.
    case get_x': (ls1 x')=> [v|] //; rewrite renameoE /= names_disjointE //.
    rewrite supp_fperm2; case: ifP=> _; first by rewrite /fdisjoint fset0I.
    apply/fdisjointP=> i'' /fset2P [->|->] {i''}.
      have := freshP (names (ls1, h1)) : i \notin names (ls1, h1).
      apply: contra=> Pi; apply/fsetUP; left=> /=.
      by apply/namesmP; eapply PMFreeNamesVal; eauto.
    have := freshP (names (unionm ls1 ls2, unionm h1 h2))
              : i' \notin names (unionm ls1 ls2, unionm h1 h2).
    apply: contra=> Pi'; apply/fsetUP; left=> /=.
    have ? : unionm ls1 ls2 x' = Some v by rewrite unionmE get_x'.
    by apply/namesmP; eapply PMFreeNamesVal; eauto.
  rewrite re_h1.
  have: fsubset (names (domm (init_block h1 i' n))) (i' |: names (domm h1)).
    rewrite /init_block domm_union namesfsU.
    apply/fsubsetP=> i'' /fsetUP [/namesfsP [p /dommP [v Pv] Pi'']|].
      move: Pv; rewrite mkpartmapfE.
      case: ifP Pi''=> // /mapP [off Poff ->]; rewrite in_fsetU in_fset0 orbF.
      by move=> /= /namesnP <- _; rewrite in_fsetU1 eqxx.
    by move=> h; rewrite in_fsetU1 orbC h.
  move=> /fsubsetP sub; apply/fdisjointP=> i'' /sub /fsetU1P [->{i''}|].
    have := freshP (names (unionm ls1 ls2, unionm h1 h2))
            : i' \notin names (unionm ls1 ls2, unionm h1 h2).
    apply: contra=> Pi'; apply/fsetUP; right=> /=; apply/namesmP.
    rewrite fdisjointC in dis; move/fdisjointP/(_ _ Pi') in dis.
    case/namesfsP: Pi'=> [p /dommP [v Pv] Pi'].
    have ?: unionm h1 h2 p = Some v.
      rewrite unionmE; case get_h1: (h1 p) => [v'|] //=.
      suff : ~~ true by [].
      apply: contra dis=> _; apply/namesfsP; exists p=>//.
      by apply/dommP; eauto.
    by eapply PMFreeNamesKey; eauto.
  by move: i''; apply/fdisjointP.
- move=> /= sub; case eval_e: eval_expr=> [| |p|] //=.
  case free_p: free=> [h'|] // [<- <-] // dis.
  have dis': fdisjoint (domm h1) (domm h2).
    apply/fdisjointP=> p' Pp'.
    have {Pp'} Pp': p'.1 \in names (domm h1).
      apply/namesfsP; exists p'=> //.
      by rewrite in_fsetU; apply/orP; left; apply/namesnP.
    move: (fdisjointP _ _ dis _ Pp'); apply: contra=> {Pp'} Pp'.
    by apply/namesfsP; exists p'=> //; apply/namesnP.
  move: free_p; rewrite /free -!lock.
  case: fpickP=> [p' /eqP Pp' /dommP [v Pv]|] //= [eh'].
  exists 1; rewrite !rename1.
    rewrite eval_expr_unionm // eval_e -!lock -eh'.
    case: fpickP=> [p'' /eqP Pp'' /dommP [v' Pv']|] /=.
      rewrite filterm_union //; congr Done; congr unionm.
      apply/eq_partmap=> p'''; rewrite filtermE.
      case get_p''': (h2 _) => [v''|] //=.
      have [Pe|] //= := altP eqP.
      have: p'.1 \in names (domm h1).
        apply/namesfsP; exists p'; last by apply/namesnP.
        by apply/dommP; eauto.
      move=> /(fdisjointP _ _ dis _); rewrite {}Pp' -{}Pe=> Pp'''.
      apply/eqP; apply: contra Pp'''=> _; apply/namesfsP.
      exists p'''; last by apply/namesnP.
      by apply/dommP; eauto.
    move=> /(_ p'); rewrite mem_domm unionmE Pv => /(_ erefl).
    by rewrite Pp' eqxx.
  suff sub': {subset names (domm h') <= names (domm h1)}.
    rewrite -eh' in sub' *.
    by apply/fdisjointP=> i /sub'/(fdisjointP _ _ dis _).
  suff sub': {subset domm h' <= domm h1}.
    rewrite -eh' in sub' *.
    by move=> i /namesfsP [p'' /sub' Pp'' Pi]; apply/namesfsP; eauto.
  by subst h'; apply/fsubsetP/domm_filter.
- by move=> _ [<- <-] dis; exists 1; rewrite !rename1.
- rewrite /= fsubUset=> /andP [sub1 sub2].
  case eval_c1: eval_com=> [ls' h'| |] //= eval_c2 dis.
  have [pm eval_c1' dis'] := IH _ _ _ _ _ sub1 eval_c1 dis.
  have [pm' eval_c2'] := renaming ls' h' c2 k pm.
  rewrite eval_c2 renamerE in eval_c2'.
  rewrite -(eval_com_domm sub1 eval_c1)
           (_ : domm ls' = domm (rename pm ls')) in sub2; last first.
    by rewrite domm_rename renamefsE -{1}(imfset_id (domm ls')).
  have [pm'' eval_c2'' dis''] := IH _ _ _ _ _ sub2 eval_c2' dis'.
  by exists (pm'' * pm'); rewrite -!renameD // eval_c1'.
- rewrite /= 2!fsubUset -andbA=> /and3P [sub_e sub_1 sub_2].
  case eval_e: eval_expr=> [b| | |] //=.
  have {sub_1 sub_2} sub_c: fsubset (vars_c (if b then c1 else c2)) (domm ls1).
    by case: b eval_e.
  move=> eval_c dis.
  have [pm eval_c' eval_e'] := IH _ _ _ _ _ sub_c eval_c dis.
  by exists pm; rewrite // eval_expr_unionm // eval_e.
rewrite /= fsubUset=> /andP [sub_e sub_c].
case eval_e: eval_expr=> [b| | |] //=.
set c' := if b then Seq c (While e c) else Skip.
have sub_c' : fsubset (vars_c c') (domm ls1).
  rewrite /c' /=; case: (b)=> //; rewrite ?fsub0set //.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub_e sub_c.
move=> eval_c' dis.
have [pm eval_c'' dis'] := IH _ _ _ _ _ sub_c' eval_c' dis.
by exists pm; rewrite // eval_expr_unionm // eval_e.
Qed.

Lemma frame_loop ls1 h1 ls2 h2 c k :
  fsubset (vars_c c) (domm ls1) ->
  eval_com ls1 h1 c k = NotYet ->
  fdisjoint (names (domm h1)) (names (domm h2)) ->
  eval_com (unionm ls1 ls2) (unionm h1 h2) c k = NotYet.
Proof.
elim: k ls1 h1 c => [//=|k IH] ls1 h1 c.
case: c=> [x e|x e|e e'|x e|e| |c1 c2|e c1 c2|e c] //.
- (* Load *)
  rewrite fsubU1set=> /andP [Px Pe] /= eval_c dis.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  by case get_p: (h1 p)=> [v|] //.
- (* Store *)
  rewrite fsubUset=> /andP [Pe Pe'] /= eval_c dis.
  case eval_e: eval_expr eval_c=> [| |p|] //.
  by rewrite /updm; case get_p: (h1 p)=> [v|] //=.
- (* Alloc *)
  rewrite fsubU1set=> /andP [Px Pe] /=.
  by case eval_e: eval_expr=> [ | [n|] | |].
- (* Free *)
  move=> /= sub; case eval_e: eval_expr=> [| |p|] //=.
  by case free_p: free=> [h'|].
- (* Seq *)
  rewrite /= fsubUset=> /andP [sub1 sub2].
  case eval_c1: eval_com=> [ls' h'| |] //= eval_c2 dis; last by rewrite IH.
  have [pm eval_c1' dis'] := frame_ok ls2 sub1 eval_c1 dis.
  rewrite eval_c1' IH; eauto.
    rewrite domm_rename renamefsE (eq_imfset (_ : rename pm =1 id)) //.
    by rewrite imfset_id (eval_com_domm sub1 eval_c1).
  have [pm' ->] := renaming ls' h' c2 k pm.
  by rewrite eval_c2.
- (* If *)
  rewrite /= 2!fsubUset -andbA=> /and3P [sub_e sub_1 sub_2].
  case eval_e: eval_expr=> [b| | |] //=.
  have {sub_1 sub_2} sub_c: fsubset (vars_c (if b then c1 else c2)) (domm ls1).
    by case: b eval_e.
  by move=> eval_c dis; rewrite eval_expr_unionm // eval_e IH.
(* While *)
rewrite /= fsubUset=> /andP [sub_e sub_c].
case eval_e: eval_expr=> [b| | |] //=.
set c' := if b then Seq c (While e c) else Skip.
have sub_c' : fsubset (vars_c c') (domm ls1).
  rewrite /c' /=; case: (b)=> //; rewrite ?fsub0set //.
  by rewrite /= fsetUC -fsetUA fsetUid fsubUset sub_e sub_c.
by move=> eval_c' dis; rewrite eval_expr_unionm // eval_e IH.
Qed.

End Def.
