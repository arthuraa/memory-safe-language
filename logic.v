Require Import Coq.Unicode.Utf8.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.choice.
Require Import Ssreflect.seq.

Require Import MathComp.ssrnum MathComp.ssrint MathComp.ssralg MathComp.bigop.

Require Import CoqUtils.ord CoqUtils.fset CoqUtils.partmap CoqUtils.fperm.
Require Import CoqUtils.nominal CoqUtils.string.

Require Import basic structured.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.

Local Open Scope fset_scope.
Local Open Scope state_scope.

Implicit Types (s : state) (A : {fset name}) (ls : locals) (h : heap).

(** Program specifcations are indexed by an element of [effect], which
tells what can happen during the execution of a program. As defined in
detail later, [Total] gives a total correctness result; [Loop] says
that the program can enter an infinite loop; [Err] says that an error
can occur during execution, but that the program will necessarily
terminate; and [LoopErr] combines [Loop] and [Err]. *)

Inductive effect :=
| Total
| Loop
| Err
| LoopErr.

Implicit Type ef : effect.

Definition effect_eq ef ef' :=
  match ef, ef' with
  | Total, Total | Loop, Loop | Err, Err | LoopErr, LoopErr => true
  | _, _ => false
  end.

Lemma effect_eqP : Equality.axiom effect_eq.
Proof. by case=> [] [] /=; constructor. Qed.

Definition effect_eqMixin := EqMixin effect_eqP.
Canonical effect_eqType := Eval hnf in EqType effect effect_eqMixin.

Definition effect_leq ef ef' :=
  nosimpl match ef, ef' with
  | Total, _
  | Loop, Loop
  | Err, Err
  | _, LoopErr => true
  | _, _ => false
  end.

Notation "ef ⊑ ef'" := (effect_leq ef ef') (at level 70, no associativity).
Notation "ef ⊏ ef'" :=
  ((ef != ef') && (ef ⊑ ef')) (at level 70, no associativity).

(** Represent predicates with states. We say that [approx s1 s2] when
[s2] can be obtained from [s1] by restricting names and removing local
bindings. NB: Making it possible to "open" local names in
specifications seems to require some work to be compatible with the
frame rule, so we are not adopting this for now. *)

CoInductive approx s1 s2 : Prop :=
| Approx A1 ls1 A2 ls2 h
  of s1 = mask A1 (ls1, h)
  &  s2 = mask A2 (ls2, h)
  &  fsubset A2 A1
  &  (forall x, ls2 x -> ls1 x = ls2 x).

(** Alternate formulation that provides additional useful hypotheses. *)
CoInductive approx_sub s1 s2 : Prop :=
| ApproxSub A1 ls1 A2 ls2 h
  of s1 = mask A1 (ls1, h)
  &  s2 = mask A2 (ls2, h)
  &  fsubset A1 (names (ls1, h))
  &  fsubset A2 (names (ls2, h))
  &  fsubset A2 A1
  &  (forall x, ls2 x -> ls1 x = ls2 x).

Lemma approxP s1 s2 : approx s1 s2 <-> approx_sub s1 s2.
Proof.
split; case; last by move=> *; econstructor; eauto.
move=> /= A1 ls1 A2 ls2 h -> -> sub12 Pls.
have sub12': fsubset (names (ls2, h)) (names (ls1, h)).
  apply/fsubsetP=> i /fsetUP /= [in_ls|in_h]; apply/fsetUP=> /=; last by auto.
  left; case/namesmP: in_ls=> [???|x v Pget in_v]; first by rewrite namesT.
  apply/fsetUP; right; apply/namesfsP; exists v=> //.
  by apply/codommP; exists x; rewrite -Pget; apply: Pls; rewrite Pget.
move: {sub12 sub12'} (fsetISS sub12 sub12').
by rewrite maskE (maskE A2)=> sub12; econstructor; eauto; try apply: fsubsetIr.
Qed.

Lemma approxss s : approx s s.
Proof.
case: s / boundP=> [/= A [ls h] sub]; econstructor=> //.
exact: fsubsetxx.
Qed.

Lemma approx_trans s2 s1 s3 : approx s1 s2 -> approx s2 s3 -> approx s1 s3.
Proof.
case/approxP=> [/= A1 ls1 A2 ls2 h -> -> sub1 sub2 sub12 Pls12 {s1 s2}].
case/approxP=> [/= A2' ls2' A3 ls3 h' e2 -> sub2'].
have {sub2'} eA2: A2' = A2 by rewrite -(namesbE sub2) e2 namesbE.
rewrite {}eA2 {A2'} in e2 *.
case/maskP: e2=> // pm dis [<- <-] {ls2' h'} sub3 sub23 Pls23.
have ->: mask A3 (ls3, rename pm h) = mask A3 (rename pm^-1%fperm ls3, h).
  apply/maskP=> //; exists pm^-1%fperm.
    by rewrite supp_inv fdisjointC (fdisjoint_trans sub23) // fdisjointC.
  by rewrite renamepE /= renameK.
econstructor; eauto; first exact: (fsubset_trans sub23).
move=> /= x Pls3; move: Pls3 (Pls23 x) (Pls12 x); rewrite !renamemE !renameT.
case: (ls3 x)=> [v3|] //= _ /(_ erefl).
by case: (ls2 x)=> [v2|] //= <- /(_ erefl) ->; rewrite renameK.
Qed.

Lemma approx_vars s1 s2 :
  approx s1 s2 -> fsubset (vars_s s2) (vars_s s1).
Proof.
case=> [/= A1 ls1 A2 ls2 h -> -> {s1 s2} sub Pls].
rewrite !vars_sE.
by apply/fsubsetP=> x; rewrite !mem_domm => in2; rewrite Pls.
Qed.

(** Specify whether the result of executing some program is compatible
with its expected output given a set of allowed effects [ef]. *)

Definition compat ef r s :=
  match r with
  | Done s' => s' == s
  | Error => Err ⊑ ef
  | NotYet => Loop ⊑ ef
  end.

Lemma compatE ef r s :
  compat ef r s =
  [|| r == Done s, (r == Error) && (Err ⊑ ef) | (r == NotYet) && (Loop ⊑ ef)].
Proof. by case: r => [s'| |] //=; rewrite orbF. Qed.

CoInductive compat_spec ef r s : Prop :=
| CompatDone of r = Done s
| CompatErr  of r = Error & Err ⊑ ef
| CompatLoop of r = NotYet & Loop ⊑ ef.

Lemma compatP ef r s :
  reflect (compat_spec ef r s) (compat ef r s).
Proof.
rewrite compatE; apply/(iffP or3P).
- move=> [/eqP ->|/andP [/eqP -> ?]|/andP [/eqP -> ?]];
  econstructor (solve [eauto]).
move=> [->|[-> ?]|[-> ?]]; econstructor (solve [eauto]).
Qed.

Lemma compat_leq ef ef' r s :
  ef ⊑ ef' ->
  compat ef r s ->
  compat ef' r s.
Proof. by case: r ef ef' => [s'| |] [] []. Qed.

(** Definition of triples proper. [triple ef s1 c s2] states that
running [c] on [s1] will yield results that are compatible with the
effects in [ef], provided that we allow the program to run for at
least a minimum number of [n0] steps. *)

Definition triple ef s1 c s2 :=
  exists n0, forall n, n0 <= n ->
    compat ef (eval_com bound_sem s1 c n) s2.

Lemma triple_leq ef ef' s1 c s2 :
  ef ⊑ ef' ->
  triple ef s1 c s2 ->
  triple ef' s1 c s2.
Proof. by move=> /compat_leq Pef [n0 Pn0]; exists n0=> ??; eauto. Qed.

Lemma triple_skip ef s : triple ef s Skip s.
Proof.
apply: (triple_leq (erefl : Total ⊑ ef)).
by exists 1=> - [|n] //=.
Qed.

Lemma triple_seq ef s1 c1 s2 c2 s3 :
  triple ef s1 c1 s2 ->
  triple ef s2 c2 s3 ->
  triple ef s1 (Seq c1 c2) s3.
Proof.
move=> [n1 t1] [n2 t2]; exists (maxn n1 n2).+1=> - [|n] //=; rewrite ltnS.
move=> ln; move: (t1 _ (leq_trans (leq_maxl _ _) ln)).
case ev1: eval_com=> [s2'| |] //= /eqP ->.
by apply: t2=> //; apply: (leq_trans (leq_maxr _ _) ln).
Qed.

Lemma triple_frame ef s1 c s1' s2 :
  fsubset (vars_c c) (vars_s s1) ->
  (if Err ⊑ ef then fdisjoint (names s1) (pub s2)
   else fdisjoint (pub s1) (pub s2)) ->
  triple ef s1 c s1' ->
  triple ef (s1 * s2) c (s1' * s2).
Proof.
move=> sub dis [n0 t]; exists n0=> n ln.
have dis': fdisjoint (pub s1) (pub s2).
  case: ifP dis=> // _ dis.
  by apply: (fdisjoint_trans (pub_names s1)).
case/(_ _ ln)/compatP: t => [] ev.
- by rewrite (frame_ok sub dis' ev) /=.
- by move=> t; rewrite t in dis; rewrite (frame_error sub dis ev).
by rewrite (frame_loop sub dis' ev).
Qed.

Lemma triple_restriction e A f c f' :
  (forall n, n \notin A -> triple e (f n) c (f' n)) ->
  triple e (new A f) c (new A f').
Proof.
move=> /(_ _ (freshP A)) [n0 t]; exists n0.
move=> n /t/compatP [] ev.
- by rewrite (restriction_ok ev) /=.
- by rewrite (restriction_error ev) /=.
by rewrite (restriction_loop ev) /=.
Qed.

Definition eval_exprb e (s : state) : option value :=
  oexpose (mapb (fun ps => eval_expr true ps.1 e) s).

Lemma eval_exprbE e A ls h :
  eval_exprb e (mask A (ls, h))
  = (if fsubset (names (eval_expr true ls e)) A then
       Some (eval_expr true ls e)
     else None).
Proof.
rewrite /eval_exprb mapbE /=; last first.
  by move=> {ls h} s [ls h] /=; rewrite rename_eval_expr.
by rewrite oexposeE.
Qed.

Lemma triple_if e s ex ct ce s' :
  match eval_exprb ex s with
  | Some (VBool b) => triple e s (if b then ct else ce) s'
  | _ => False
  end ->
  triple e s (If ex ct ce) s'.
Proof.
case ev_ex: eval_exprb=> [[b| | |]|] // [n0 t].
exists n0.+1=> - [|n] //; rewrite ltnS /= => /t {t}.
case: s / boundP ev_ex=> [/= A [ls h] sub].
rewrite eval_exprbE bound_eval_condE /=.
by case: ifP=> _ // [->].
Qed.

Lemma triple_while e s ex c s' :
  match eval_exprb ex s with
  | Some (VBool b) => triple e s (if b then Seq c (While ex c) else Skip) s'
  | _ => False
  end ->
  triple e s (While ex c) s'.
Proof.
case ev_ex: eval_exprb=> [[b| | |]|] // [n0 t].
exists n0.+1=> - [|n] //; rewrite ltnS /= => /t {t}.
case: s / boundP ev_ex=> [/= A [ls h] sub].
rewrite eval_exprbE bound_eval_condE /=.
by case: ifP=> _ // [->].
Qed.

Lemma setl_key : unit. Proof. exact: tt. Qed.
Definition setl_def (s : state) x v :=
  mapb_fs (names v) (fun ps => (setm ps.1 x v, ps.2)) s.
Definition setl := locked_with setl_key setl_def.

Lemma setlE A ps x v :
  fsubset (names v) A ->
  fsubset A (names ps) ->
  setl (mask A ps) x v = mask A (setm ps.1 x v, ps.2).
Proof.
move=> sub1 sub2; rewrite [setl]unlock /setl_def mapb_fsE //.
- by congr mask; apply/eqP.
- move=> pm /= dis [ls h] /=.
  rewrite renamepE /=; congr pair.
  rewrite renamem_set; congr setm.
  by rewrite names_disjointE.
by apply: fsubIset; rewrite sub1.
Qed.

Lemma setlx x v v' : setl (x ::= v) x v' = (x ::= v').
Proof.
have P:
  forall v'' : value, names (setm emptym x v'', emptym : heap) = names v''.
  move=> v''; rewrite {1}/names /= /prod_names /= namesm_empty fsetU0.
  apply/eq_fset=> n; apply/idP/idP.
    case/namesmP; first by move=> ???; rewrite namesT in_fset0.
    move=> x' v'''; rewrite setmE emptymE.
    by case: eqP=> // _ [<-].
  move=> n_in_v'; apply/fsetUP; right; apply/namesfsP; exists v''=> //.
  by apply/codommP; exists x; rewrite setmE eqxx.
rewrite [setl]unlock /setl_def /locval /= mapb_fsE /=.
- rewrite [X in (X, _)](_ : _ = setm emptym x v'); last first.
    by apply/eq_partmap=> x'; rewrite !setmE; case: eqP.
  rewrite maskE P; congr mask; apply/eqP; rewrite eqEfsubset fsubsetIr /=.
  by rewrite fsubsetI fsubsetxx andbT; apply: fsubsetU; rewrite fsubsetxx.
- move=> pm dis [/= ls h].
  by rewrite renamepE /= renamem_set [_ _ v']names_disjointE.
by rewrite P fsubIset // fsubsetxx orbT.
Qed.

Lemma triple_assn s x e v :
  eval_exprb e s = Some v ->
  triple Total s (Assn x e) (setl s x v).
Proof.
move=> /= ev; exists 1=> - [|n] //= _.
case: s / boundP ev => [/= A [ls h] sub].
rewrite eval_exprbE; case: ifP => // sub' [ev].
move: sub'; rewrite bound_assnE /= ev => sub'.
by rewrite setlE //.
Qed.

Definition loadb (s : state) (ptr : name * int) :=
  odflt None (oexpose (mapb_fs (names ptr)
                               (fun s : locals * heap => s.2 ptr) s)).

Lemma loadbE A ps ptr :
  fsubset (names ptr) A ->
  fsubset A (names ps) ->
  loadb (mask A ps) ptr =
  if fsubset (names (ps.2 ptr)) A then
    ps.2 ptr
  else None.
Proof.
move=> sub1 sub2; rewrite /loadb mapb_fsE.
- move: (sub1); rewrite {1}/fsubset; move/eqP=> ->.
  by rewrite oexposeE; case: ifP.
- move=> pm /= dis [ls h] /=.
  by rewrite renamemE [rename _ ptr]names_disjointE // supp_inv.
by apply: fsubIset; rewrite sub1.
Qed.

Lemma loadbp i i' vs n :
  loadb (i :-> vs) (i', n) =
  if i' == i then
    if n is Posz n then nth None [seq Some v | v <- vs] n
    else None
  else None.
Proof.
rewrite /loadb [blockat]unlock /= {1}/names /= /prod_names /= namesT fsetU0.
rewrite namesnE mapb_fsE /=.
- rewrite oexposeE mkpartmapfE.
  case: eqP=> [->{i'}|ne].
    rewrite fsetU1E fsetUA fsetUid -fsetU1E.
    case: n=> [n|n] /=.
      rewrite mem_map=> [|?? [<-]] //; rewrite mem_iota add0n leq0n /=.
      case: (ifP (n < size vs)) => [lvs|gvs].
        rewrite {1}/names /= ifT /= ?(nth_map VNil None _ lvs) //.
        apply/fsubsetP=> i' Pi'; apply/fsetU1P; right.
        apply/namessP; exists (nth VNil vs n)=> //.
        by apply/(nthP VNil); eauto.
      rewrite {1}/names /= fsub0set /= nth_default //.
      by rewrite size_map leqNgt gvs.
    rewrite (@ifF _ (_ \in _)); first by rewrite /names /= fsub0set.
    by apply/negbTE/mapP=> - [? ?].
  rewrite (@ifF _ (_ \in _)); first by rewrite /names /= fsub0set.
  apply/negbTE/mapP=> - [? ?]; congruence.
- move=> pm dis /= [ls h] /=.
  rewrite renamemE [rename _ (_, _)]names_disjointE //.
  by rewrite supp_inv /names /= /prod_names /= namesT fsetU0.
apply/fsubsetP=> i'' /fsetIP [/fset1P -> {i''}].
case/fsetUP=> [] /=; first by rewrite namesm_empty.
rewrite namesm_mkpartmapf=> /fsetUP [] /namessP.
  case=> [p /mapP [? ? ->] /fsetUP []] /=; last by rewrite namesT.
  by move=> /namesnP ->; apply/fsetU1P; auto.
case=> [v /mapP [p /mapP [n']]].
rewrite mem_iota leq0n /= add0n => Pn' -> {p} /= -> Pi'.
apply/fsetU1P; right; apply/namessP; exists (nth VNil vs n')=> //.
by apply/(nthP VNil); eauto.
Qed.

Lemma loadbl v s1 s2 ptr :
  loadb s1 ptr = Some v ->
  loadb (s1 * s2) ptr = Some v.
Proof.
case: s1 s2 / (fbound2P (names ptr))
  => [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2 sub3 sub4].
admit.
Qed.

Lemma triple_load s x e ptr v :
  eval_exprb e s = Some (VPtr ptr) ->
  loadb s ptr = Some v ->
  triple Total s (Load x e) (setl s x v).
Proof.
move=> /= ev_ex get; exists 1=> - [|n] //= _.
case: s / boundP ev_ex get => [/= A [ls h] sub].
rewrite eval_exprbE; case: ifP=> // sub' [ev].
rewrite ev in sub'; rewrite loadbE //=.
rewrite bound_loadE /= ev.
case: ifP=> // sub'' get; rewrite get /=.
by rewrite get in sub''; rewrite setlE.
Qed.

Definition storeb (s : state) (ptr : name * int) v :=
  obound (locked mapb_fs _ _ (names ptr :|: names v)
                 (fun ps => omap (fun h => (ps.1, h)) (updm ps.2 ptr v)) s).

Lemma storebE A ps ptr v :
  fsubset (names ptr) A ->
  fsubset (names v) A ->
  fsubset A (names ps) ->
  storeb (mask A ps) ptr v =
  omap (fun h => mask A (ps.1, h)) (updm ps.2 ptr v).
Proof.
move: ps ptr v => [/= ls h] ptr v sub1 sub2 sub3.
have sub4: fsubset (names ptr :|: names v) A by rewrite fsubUset sub1.
rewrite /storeb -!lock /= mapb_fsE /= ?oboundE.
- by move: sub4; rewrite {1}/fsubset => /eqP ->; case: updm.
- move=> pm /= dis {ls h sub3} [ls' h'] /=.
  have dis1: fdisjoint (supp pm) (names ptr).
    rewrite fdisjointC in dis; rewrite fdisjointC.
    by apply: (fdisjoint_trans (fsubsetUl _ (names v))).
  have dis2: fdisjoint (supp pm) (names v).
    rewrite fdisjointC in dis; rewrite fdisjointC.
    by apply: (fdisjoint_trans (fsubsetUr (names ptr) _)).
  rewrite /updm renamemE [rename _ ptr]names_disjointE ?supp_inv //.
  case get: (h' ptr)=> [v'|] //=.
  rewrite {1}/rename /= renamepE /= renamem_set.
  by rewrite [rename _ ptr]names_disjointE // [rename _ v]names_disjointE.
by apply/fsubIset; rewrite sub4.
Qed.

Lemma triple_store s e e' ptr v s' :
  eval_exprb e s = Some (VPtr ptr) ->
  eval_exprb e' s = Some v ->
  storeb s ptr v = Some s' ->
  triple Total s (Store e e') s'.
Proof.
case: s / boundP=> [/= A [ls h] sub] ev_e ev_e' st.
exists 1=> - [|n] //= _; rewrite bound_storeE /=.
move: ev_e ev_e' st.
rewrite eval_exprbE; case: ifP=> // sub' [e_ptr]; rewrite e_ptr in sub' *.
rewrite eval_exprbE; case: ifP=> // sub'' [e_v]; rewrite e_v in sub'' *.
rewrite storebE //= /updm.
by case: (h ptr)=> [v'|] //= [<-].
Qed.

Definition lh i (vs : seq value) :=
  if vs is [::] then VNil else VPtr (i, 0)%R.

Fixpoint lb i vs :=
  if vs is v :: vs' then
    new (i |: names vs)
        (fun i' => i :-> [:: v; lh i' vs'] * lb i' vs')
  else emp.

Lemma rename_lh pm i vs :
  rename pm (lh i vs) = lh (pm i) (rename pm vs).
Proof. by case: vs. Qed.

Lemma names_lh i vs : names (lh i vs) = if nilp vs then fset0 else fset1 i.
Proof. by case: vs=> //= _ _; rewrite namesvE. Qed.

Lemma vars_lb i vs : vars_s (lb i vs) = fset0.
Proof.
elim: vs i => /= [|v vs IH] /= i; first by rewrite vars_emp.
by rewrite /new vars_s_hide vars_s_stateu vars_s_blockat IH fsetU0.
Qed.

Lemma pub_lb i vs : pub (lb i vs) = if vs is [::] then fset0 else fset1 i.
Proof.
elim: vs i=> //= [|v vs IH] i; first by rewrite pub_emp.
rewrite /new pub_hide.
move: (fresh _) (freshP (i |: names (v :: vs)))=> i'.
rewrite in_fsetU1 namess1 in_fsetU !negb_or => /and3P [ii' iv ivs].
rewrite pubU IH pub_blockat.
case: vs {IH ivs} => [|v' vs'] //=.
  rewrite fsetU0; apply/eq_fset=> i''.
  rewrite in_fsetD1 in_fset1.
  have [->|] //= := altP (i'' =P i').
  by rewrite (negbTE ii').
apply/eq_fset=> i''; rewrite in_fsetD1 in_fsetU !in_fset1.
have [->|] //= := altP (i'' =P i').
  by rewrite (negbTE ii').
by rewrite orbF.
Qed.

Lemma names_lb i vs :
  names (lb i vs) = pub (lb i vs) :|: names vs.
Proof.
elim: vs i => [|v vs IH] i /=.
  by rewrite names_emp pub_emp fset0U namess0.
rewrite /new.
move: (fresh _) (freshP (i |: names (v :: vs)))=> i'.
rewrite namess1 => nin.
move: (nin); rewrite in_fsetU1 in_fsetU !negb_or=> /and3P [ii' ninv ninvs].
rewrite names_hide names_stateu; first last.
  rewrite pub_blockat pub_lb; case: (vs)=> // _ _.
    by apply/fdisjointP=> i'' /fset1P ->; rewrite in_fset1 eq_sym.
  by rewrite !vars_s_blockat fdisjoint0.
rewrite pub_hide pubU pub_blockat names_blockat /= namessE /= fsetU0 {}IH.
rewrite fsetU1E !fsetD1U -!fsetUA; congr fsetU.
have ->: names (lh i' vs) :\ i' = fset0.
  by rewrite names_lh; case: (vs)=> //= ??; rewrite fsetD1E fsetDv.
have ->: pub (lb i' vs) :\ i' = fset0.
  by rewrite pub_lb; case: (vs)=> //= ??; rewrite fsetD1E fsetDv.
rewrite !fset0U -fsetD1U.
apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr /=.
apply/fsubsetP=> i'' inv; rewrite in_fsetD1 inv andbT.
by apply: contraTN inv => /eqP ->; rewrite in_fsetU negb_or ninv.
Qed.

Lemma rename_lb pm i vs :
  rename pm (lb i vs) = lb (pm i) (rename pm vs).
Proof.
elim: vs pm i=> [|v vs IH] pm i /=.
  by apply/names0P; rewrite names_emp.
rewrite rename_new; last first.
  move=> {pm} pm dis /= i'.
  rewrite rename_stateu rename_blockat /= renamenE IH.
  move: dis; rewrite fsetU1E namess1 2!fdisjointUr fdisjoints1.
  case/and3P=> [/suppPn pm_i disv disvs].
  rewrite pm_i renamesE /= names_disjointE //.
  by rewrite rename_lh /= (names_disjointE disvs).
rewrite (_ : pm i |: _ = pm @: (i |: names (v :: vs))); last first.
  by rewrite imfsetU1 -names_rename renamesE.
set A := pm @: (i |: _).
rewrite /new /=.
move: (fresh _) (freshP A)=> n ninA /=.
rewrite rename_stateu rename_blockat renamesE /=.
by rewrite !rename_lh renamenE IH // fpermKV.
Qed.

Lemma ll_key : unit. Proof. exact: tt. Qed.
Definition ll_def x vs : state :=
  new (names vs) (fun i => (x ::= lh i vs) * lb i vs).
Definition ll := locked_with ll_key ll_def.

Lemma vars_ll x vs : vars_s (ll x vs) = fset1 x.
Proof.
rewrite [ll]unlock /new vars_s_hide vars_s_stateu vars_s_locval.
by rewrite vars_lb fsetU0.
Qed.

Lemma pub_ll x vs : pub (ll x vs) = fset0.
Proof.
rewrite [ll]unlock /new pub_hide.
rewrite pubU pub_locval fset0U pub_lb.
by case: vs=> // ??; rewrite fsetD1E fsetDv.
Qed.

Lemma names_ll x vs : names (ll x vs) = names vs.
Proof.
rewrite [ll]unlock /new names_hide.
rewrite names_stateu ?vars_s_locval ?vars_lb 1?fdisjointC ?fdisjoint0 //.
  rewrite names_locval names_lh names_lb pub_lb.
  case: vs=> [|v vs] /=; first by rewrite !fset0U namess0 fsetD1E fset0D.
  move: (_ :: _) (fresh _) (freshP (names (v :: vs))) => {v vs} vs i fr.
  rewrite fsetUA fsetUid fsetD1U fsetD1E fsetDv fset0U.
  apply/eqP; rewrite eqEfsubset fsubD1set fsetU1E fsubsetUr /=.
  apply/fsubsetP=> i' in_v; rewrite in_fsetD1.
  case: eqP in_v => [->|] //=.
  by rewrite (negbTE fr).
by rewrite pub_locval fdisjointC fdisjoint0.
Qed.

Lemma ll0 x : ll x [::] = x ::= VNil.
Proof.
rewrite [ll]unlock /ll_def /= -[RHS]stateus0 -[RHS]new_const namess0.
by congr new; rewrite stateus0 names_locval.
Qed.

Lemma ll1 x v vs :
  ll x (v :: vs) =
  new (names v :|: names vs)
      (fun i => new (i |: names v :|: names vs)
                    (fun i' =>
                       x ::= VPtr (i, Posz 0) *
                       i :-> [:: v; lh i' vs] *
                       lb i' vs)).
Proof.
rewrite [ll]unlock /ll_def /= namess1; apply/newP=> i Pn /=.
rewrite new_stateur.
  rewrite names_locval namesvE /= !fsetU1E !fsetUA fsetUid.
  by apply/newP=> ??; rewrite stateuA.
move=> pm.
rewrite fsetU1E !fdisjointUr fdisjoints1 => /and3P [Pi Pv Pvs] i'.
rewrite !rename_stateu rename_lb rename_blockat /=.
rewrite {1}/rename /= names_disjointE // rename_lh names_disjointE //.
by rewrite -renamenE names_disjointE // namesnE fdisjoints1.
Qed.

Lemma ll1' x v vs s :
  ll x (v :: vs) * s =
  new (names v :|: names vs :|: names s)
      (fun i => new (i |: (names v :|: names vs :|: names s))
                    (fun i' =>
                       x ::= VPtr (i, Posz 0) *
                       i :-> [:: v; lh i' vs] *
                       lb i' vs *
                       s)).
Proof. admit. Qed.

Coercion Binop : binop >-> Funclass.
Coercion Var : string >-> expr.
Coercion Num : int >-> expr.

Lemma eval_exprb_new e A f :
  (forall i, i \notin A -> i \notin names (eval_exprb e (f i))) ->
  eval_exprb e (new A f) = eval_exprb e (f (fresh A)).
Proof.
move=> fr; rewrite /new.
move: (fresh _) (fr _ (freshP A))=> {A fr} i; move: (f i)=> {f} s.
case: s / (fboundP (fset1 i))=> [/= A [ls h] sub1 sub2].
rewrite hideE !eval_exprbE; case: ifPn=> [sub fresh_i|sub _].
  rewrite ifT //.
  apply/fsubsetP=> i' in_e; rewrite in_fsetD1 (fsubsetP _ _ sub _ in_e) andbT.
  by apply: contraTN in_e=> /eqP ->.
rewrite ifN //; apply: contra sub=> sub; apply: (fsubset_trans sub).
by rewrite fsubD1set fsetU1E fsubsetUr.
Qed.

Lemma eval_exprb_nil s : eval_exprb ENil s = Some VNil.
Proof.
case: s / boundP=> [/= A [ls h] sub].
by rewrite eval_exprbE /= fsub0set.
Qed.

Lemma eval_exprb_var x v : eval_exprb (Var x) (x ::= v) = Some v.
Proof.
by rewrite /locval eval_exprbE /= setmE eqxx /= fsubsetxx.
Qed.

Lemma eval_exprb_varl x s1 s2 :
  x \notin vars_s s2 ->
  eval_exprb (Var x) (s1 * s2) = eval_exprb (Var x) s1.
Proof.
case: s1 s2 / bound2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite stateuE // !eval_exprbE /= vars_sE /= unionmE => /dommPn ->.
case get: (ls1 _)=> [v|] //=; last by rewrite namesvE !fsub0set.
case/and3P: mf=> [/fsubsetP mf _ _].
rewrite [fsubset _ _ in LHS](_ : _ = fsubset (names v) A1) //.
apply/idP/idP; last by move=> h; apply/fsubsetU; rewrite h.
move=> /fsubsetP sub {sub1 sub2}; apply/fsubsetP=> i in_v.
case/(_ _ in_v)/fsetUP: sub=> // in_A2; apply: mf.
rewrite in_fsetI in_A2 andbT; apply/fsetUP; left; apply/fsetUP; right=> /=.
by apply/namesfsP; exists v=> //; apply/codommP; eauto.
Qed.

Lemma eval_exprb_varl' x s1 s2 :
  x \in vars_s s1 ->
  eval_exprb (Var x) (s1 * s2) = eval_exprb (Var x) s1.
Proof.
case: s1 s2 / bound2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite stateuE // !eval_exprbE /= vars_sE /= unionmE=> /dommP [v Px].
rewrite Px /=.
case/and3P: mf=> [/fsubsetP mf _ _].
rewrite [fsubset _ _ in LHS](_ : _ = fsubset (names v) A1) //.
apply/idP/idP; last by move=> h; apply/fsubsetU; rewrite h.
move=> /fsubsetP sub {sub1 sub2}; apply/fsubsetP=> i in_v.
case/(_ _ in_v)/fsetUP: sub=> // in_A2; apply: mf.
rewrite in_fsetI in_A2 andbT; apply/fsetUP; left; apply/fsetUP; right=> /=.
by apply/namesfsP; exists v=> //; apply/codommP; eauto.
Qed.

Lemma eval_exprb_varr x s1 s2 :
  x \notin vars_s s1 ->
  eval_exprb (Var x) (s1 * s2) = eval_exprb (Var x) s2.
Proof.
case: s1 s2 / bound2P=> [/= A1 [ls1 h1] A2 [ls2 h2] mf sub1 sub2].
rewrite stateuE // !eval_exprbE /= vars_sE /= unionmE => /dommPn -> /=.
case get: (ls2 _)=> [v|] //=; last by rewrite namesvE !fsub0set.
case/and3P: mf=> [_ /fsubsetP mf _].
rewrite [fsubset _ _ in LHS](_ : _ = fsubset (names v) A2) //.
apply/idP/idP; last by move=> h; apply/fsubsetU; rewrite h orbT.
move=> /fsubsetP sub {sub1 sub2}; apply/fsubsetP=> i in_v.
case/(_ _ in_v)/fsetUP: sub=> // in_A1; apply: mf.
rewrite in_fsetI in_A1 /=; apply/fsetUP; left; apply/fsetUP; right=> /=.
by apply/namesfsP; exists v=> //; apply/codommP; eauto.
Qed.

Lemma eval_exprb_binop v1 v2 b e1 e2 s :
  eval_exprb e1 s = Some v1 ->
  eval_exprb e2 s = Some v2 ->
  eval_exprb (Binop b e1 e2) s = Some (eval_binop b v1 v2).
Proof.
case: s / boundP=> [/= A [ls h] sub].
rewrite !eval_exprbE /=.
case: ifP=> //= sub1 [<-] {v1}; case: ifP=> //= sub2 [<-] {v2}.
by rewrite (fsubset_trans (eval_binop_names b _ _)) // fsubUset /= sub1.
Qed.

Lemma eval_exprb_num n s : eval_exprb (Num n) s = Some (VNum n).
Proof.
case: s / boundP=> [/= A [ls h] sub]; rewrite eval_exprbE /=.
by rewrite namesvE fsub0set.
Qed.

Lemma ll1_nil x v vs s :
  eval_exprb (Eq (Var x) ENil) (ll x (v :: vs) * s) = Some (VBool false).
Proof.
rewrite ll1' !eval_exprb_new; first last.
- move=> i fresh_i; rewrite eval_exprb_new -?stateuA.
    rewrite (@eval_exprb_binop (VPtr (i, Posz 0)) VNil) //= ?eval_exprb_nil //.
    by rewrite eval_exprb_varl' ?vars_s_locval ?in_fset1 // eval_exprb_var.
  move=> i' _; rewrite -!stateuA.
  rewrite (@eval_exprb_binop (VPtr (i, Posz 0)) VNil) //= ?eval_exprb_nil //.
  by rewrite eval_exprb_varl' ?vars_s_locval ?in_fset1 // eval_exprb_var.
- move=> i' _; rewrite -!stateuA.
  move: (fresh _)=> i.
  rewrite (@eval_exprb_binop (VPtr (i, Posz 0)) VNil) //= ?eval_exprb_nil //.
  by rewrite eval_exprb_varl' ?vars_s_locval ?in_fset1 // eval_exprb_var.
move: (fresh _)=> i; rewrite -!stateuA.
rewrite (@eval_exprb_binop (VPtr (i, Posz 0)) VNil) //= ?eval_exprb_nil //.
by rewrite eval_exprb_varl' ?vars_s_locval ?in_fset1 // eval_exprb_var.
Qed.

Local Open Scope string_scope.

Local Notation "c1 ;; c2" :=
  (Seq c1 c2) (at level 70, right associativity).

Definition listrev :=
  While (Neg (Eq "x" ENil))
        (Load "y" (Add "x" 1);;
         Store (Add "x" 1) "r";;
         Assn "r" "x";;
         Assn "x" "y";;
         Assn "y" ENil).

Lemma eval_exprb_neg e s :
  eval_exprb (Neg e) s =
  match eval_exprb e s with
  | Some (VBool b) => Some (VBool (~~ b))
  | _ => Some VNil
  end.
Proof.
case: s / boundP=> [/= A [ls h] sub].
rewrite !eval_exprbE /=.
case ev: eval_expr => [b| | |]; rewrite !namesvE fsub0set //.
by case: ifP.
Qed.

Lemma setlU s1 s2 x v :
  setl (s1 * s2) x v =
  if x \in vars_s s1 then setl s1 x v * s2
  else s1 * setl s2 x v.
Proof. admit. Qed.

Lemma listrev_spec vs :
  triple Total
         (ll "x" vs * "r" ::= VNil * "y" ::= VNil)
         listrev
         ("x" ::= VNil * ll "r" (rev vs) * "y" ::= VNil).
Proof.
rewrite -(ll0 "r") -[rev vs]cats0.
elim: vs [::] => [|v vs IH] vs'.
  rewrite /rev /= !ll0 /listrev; apply: triple_while.
  rewrite eval_exprb_neg (@eval_exprb_binop VNil VNil) /=.
  - exact: triple_skip.
  - rewrite -stateuA eval_exprb_varl ?eval_exprb_var //.
    rewrite vars_s_stateu vars_ll vars_s_locval in_fsetU.
    (* FIXME: Something gets very slow if we try to proceed directly here... *)
    by rewrite negb_or; apply/andP; split; rewrite in_fset1.
  exact: eval_exprb_nil.
rewrite rev_cons cat_rcons -stateuA; apply: triple_while.
rewrite eval_exprb_neg ll1_nil /=.
apply: (triple_seq _ (IH _))=> {IH}.
rewrite [ll _ vs * _]stateuC; first last.
- rewrite pub_ll fdisjoint0 //.
- by rewrite !vars_ll; apply/fdisjointP=> x /fset1P ->; rewrite in_fset1.
rewrite -stateuA !ll1'.
rewrite names_stateu ?names_ll ?vars_ll ?vars_s_locval; first last.
- by rewrite pub_ll fdisjoint0.
- by apply/fdisjointP=> ? /fset1P ->; rewrite in_fset1.
rewrite names_locval fsetU0 names_stateu; first last.
- by rewrite pub_ll fdisjoint0.
- rewrite vars_ll vars_s_locval.
  by apply/fdisjointP=> ? /fset1P ->; rewrite in_fset1.
rewrite names_ll names_locval fsetU0.
rewrite -![_ :|: names vs' :|: _]fsetUA [names vs' :|: _]fsetUC fsetUA.
rewrite [ll]unlock /ll_def.
apply: triple_restriction=> i; rewrite !in_fsetU !negb_or -andbA.
case/and3P=> [i_v i_vs i_vs'].
apply: triple_restriction=> i'; rewrite in_fsetU1 !in_fsetU !negb_or -andbA.
case/and4P=> [ii' i'_v i'_vs i'_vs'].
apply: (triple_seq (@triple_load _ _ _ (i', Posz 1) (lh i vs) _ _)).
- rewrite (@eval_exprb_binop (VPtr (i', Posz 0)) (VNum 1)) //.
    rewrite -!stateuA eval_exprb_varl' ?eval_exprb_var //.
    by rewrite vars_s_locval in_fset1.
  by rewrite eval_exprb_num.
- apply: loadbl; apply: loadbl.
  rewrite stateuC ?vars_s_blockat ?pub_locval
          ?[fdisjoint _ fset0]fdisjointC ?fdisjoint0 //.
  by apply: loadbl; rewrite loadbp eqxx.
rewrite stateuA setlU !vars_s_stateu vars_s_locval !in_fsetU in_fset1 /=.
rewrite vars_s_blockat vars_lb vars_ll in_fset1 /=.
rewrite setlx.
rewrite newC; last first.
  move=> pm; rewrite !fdisjointUr -andbA => /and3P [disv disvs disvs'] /=.
  move=> [i i'] /=.
  rewrite !rename_stateu !rename_locval rename_blockat rename_lb.
  rewrite [_ _ (ll _ vs')]names_disjointE ?names_ll //.
  rewrite [rename _ [:: _; _]]/rename /= [rename pm v]names_disjointE //.
  by rewrite rename_lh [rename _ vs]names_disjointE //.
Qed.

End Logic.
