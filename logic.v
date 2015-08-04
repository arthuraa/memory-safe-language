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

Inductive effect :=
| No
| Loop
| Err
| LoopErr.

Definition effect_eq e e' :=
  match e, e' with
  | No, No | Loop, Loop | Err, Err | LoopErr, LoopErr => true
  | _, _ => false
  end.

Lemma effect_eqP : Equality.axiom effect_eq.
Proof. by case=> [] [] /=; constructor. Qed.

Definition effect_eqMixin := EqMixin effect_eqP.
Canonical effect_eqType := Eval hnf in EqType effect effect_eqMixin.

Definition effect_leq e e' :=
  match e, e' with
  | No, _
  | Loop, Loop
  | Err, Err
  | _, LoopErr => true
  | _, _ => false
  end.

Notation "x ⊑ y" := (effect_leq x y) (at level 70, no associativity).

Definition triple e s c s' :=
  nosimpl match e with
  | No =>
    exists n, eval_com bound_sem s c n = Done s'

  | Loop =>
    forall n, eval_com bound_sem s c n \in [:: NotYet; Done s']

  | Err =>
    exists n, eval_com bound_sem s c n \in [:: Error; Done s']

  | LoopErr =>
    forall n, eval_com bound_sem s c n \in [:: NotYet; Error; Done s']

  end.

Lemma elim_triple_strong e s1 c1 s1' s2 c2 s2' :
  (forall n,  eval_com bound_sem s1 c1 n = NotYet ->
   exists2 n', n <= n' & eval_com bound_sem s2 c2 n' = NotYet) ->
  (forall n, Err ⊑ e -> eval_com bound_sem s1 c1 n = Error ->
   exists n', eval_com bound_sem s2 c2 n' = Error) ->
  (forall n,  eval_com bound_sem s1 c1 n = Done s1' ->
   exists n', eval_com bound_sem s2 c2 n' = Done s2') ->
  triple e s1 c1 s1' -> triple e s2 c2 s2'.
Proof.
case: e=> [] /= ev_loop ev_error ev_ok.
- by case=> [n ev]; rewrite /triple /=; eauto.
- move=> ev n; move/(_ n): ev; rewrite !inE.
  case/orP=> [] /eqP ev.
    case/(_ _ ev): ev_loop=> [n' lnn' {ev} ev]; apply/orP; left.
    by rewrite (eval_com_loop lnn' ev).
  case/(_ _ ev): ev_ok=> [n' {ev} ev].
  exact: (eval_com_ok n ev).
- case=> [n]; rewrite !inE => /orP [] /eqP ev.
    case/(_ _ erefl ev): ev_error=> [n' {ev} ev].
    by exists n'; rewrite ev inE eqxx.
  case/(_ _ ev): ev_ok=> [n' {ev} ev].
  by exists n'; rewrite ev !inE eqxx orbT.
move=> ev n; move/(_ n): ev; rewrite !inE => /or3P [] /eqP ev.
- move/(_ _ ev): ev_loop => [n' lnn' {ev} ev].
  by rewrite (eval_com_loop lnn' ev).
- move/(_ _ erefl ev): ev_error=> [n' {ev} ev].
  move: (eval_com_error n ev); rewrite /refine_result.
  by case/orP=> -> //; rewrite orbT.
move/(_ _ ev): ev_ok=> [n' {ev} ev].
move: (eval_com_ok n ev); rewrite /refine_result.
by case/orP=> -> //; rewrite !orbT.
Qed.

Lemma elim_triple e s1 c1 s1' s2 c2 s2' :
  (forall n, eval_com bound_sem s1 c1 n = NotYet ->
             eval_com bound_sem s2 c2 n = NotYet) ->
  (forall n, Err ⊑ e ->
             eval_com bound_sem s1 c1 n = Error ->
             eval_com bound_sem s2 c2 n = Error) ->
  (forall n, eval_com bound_sem s1 c1 n = Done s1' ->
             eval_com bound_sem s2 c2 n = Done s2') ->
  triple e s1 c1 s1' -> triple e s2 c2 s2'.
Proof.
move=> ev_loop ev_error ev_ok.
by apply: elim_triple_strong=> [n ev|n err ev|n ev]; exists n=> //; eauto.
Qed.

Lemma triple_sub e e' s c s' :
  e ⊑ e' ->
  triple e s c s' ->
  triple e' s c s'.
Proof.
case: e e'=> [] [] //= _.
- case=> [n en] n'.
  move: (eval_com_leq bound_sem s c (leq_maxr n n')).
  move: (eval_com_leq bound_sem s c (leq_maxl n n')).
  rewrite en /refine_result
    => /orP [/eqP en' | /eqP en'] /orP [/eqP ->|/eqP en''] //.
  by rewrite en' !inE en'' eqxx orbT.
- case=> [n en]; exists n; by rewrite en !inE eqxx orbT.
- case=> [n en] n'.
  move: (eval_com_leq bound_sem s c (leq_maxr n n')).
  move: (eval_com_leq bound_sem s c (leq_maxl n n')).
  rewrite en /refine_result
    => /orP [/eqP en' | /eqP en'] /orP [/eqP ->|/eqP en''] //.
  by rewrite en'' -en' !inE eqxx orbT.
- move=> P n; move/(_ n): P; rewrite !inE orbA [_ || _ as X in X || _]orbC.
  by rewrite -orbA=> ->; rewrite orbT.
case=> [n n_term] n'.
move: (eval_com_leq bound_sem s c (leq_maxr n n')).
move: n_term (eval_com_leq bound_sem s c (leq_maxl n n')).
by rewrite 2!inE=> /orP [/eqP en|/eqP en];
rewrite en /refine_result /= => /eqP <- /orP [/eqP ->| /eqP ->];
rewrite !inE /=.
Qed.

Lemma triple_skip e s : triple e s Skip s.
Proof.
apply: (triple_sub (erefl : No ⊑ e)).
by exists 1=> /=.
Qed.

Lemma triple_seq e s c1 s' c2 s'' :
  triple e s c1 s' ->
  triple e s' c2 s'' ->
  triple e s (Seq c1 c2) s''.
Proof.
case: e=> /=.
- move=> [n1 e1] [n2 e2].
  exists (maxn n1 n2).+1=> /=.
  move: (eval_com_leq bound_sem s c1 (leq_maxl n1 n2)).
  rewrite e1 /refine_result /= => /eqP <-.
  move: (eval_com_leq bound_sem s' c2 (leq_maxr n1 n2)).
  by rewrite e2 /refine_result /= => /eqP <-.
- move=> P1 P2 [|n] //=; move/(_ n): P1.
  by rewrite 2!inE=> /orP [] /eqP ->.
- case=> [n1 n1_term] [n2 n2_term] /=; exists (maxn n1 n2).+1; rewrite /=.
  move: n2_term (eval_com_leq bound_sem s' c2 (leq_maxr n1 n2)).
  move: n1_term (eval_com_leq bound_sem s c1 (leq_maxl n1 n2)).
  rewrite /refine_result !inE /= => /orP [] /eqP -> /= /eqP <- //=.
  by case/orP=> [] /eqP -> /= /eqP <- /=.
move=> P1 P2 [|n] //=.
move/(_ n): P1; rewrite !inE => /or3P [] /eqP -> //=.
by move/(_ n): P2; rewrite !inE.
Qed.

Lemma triple_frame e s1 c s1' s2 :
  fsubset (vars_c c) (vars_s s1) ->
  (if Err ⊑ e then fdisjoint (names s1) (pub s2)
   else fdisjoint (pub s1) (pub s2)) ->
  triple e s1 c s1' ->
  triple e (s1 * s2) c (s1' * s2).
Proof.
move=> sub dis.
have dis': fdisjoint (pub s1) (pub s2).
  case: ifP dis=> // _ dis.
  by apply: (fdisjoint_trans (pub_names s1)).
apply: elim_triple=> [n ev|n err ev|n ev].
- by rewrite (frame_loop sub dis' ev).
- by rewrite err in dis; rewrite (frame_error sub dis ev).
by rewrite (frame_ok sub dis' ev).
Qed.

Lemma triple_restriction e A s c s' :
  finsupp A s -> finsupp A s' ->
  (forall n, n \notin A -> triple e (s n) c (s' n)) ->
  triple e (new A s) c (new A s').
Proof.
move=> fs fs'; move: (fresh _) (freshP A) => n Pn.
have R: forall n' (s : name -> state),
          n' \notin A -> finsupp A s ->
          s n' = rename (fperm2 n n') (s n).
  move=> {s s' fs fs'} n' s Pn' /(_ (fperm2 n n')) ->.
    by rewrite renamenE fperm2L.
  apply: (fdisjoint_trans (fsubset_supp_fperm2 _ _)).
  by apply/fdisjointP=> n'' /fset2P [] ->.
move=> /(_ _ Pn); apply: elim_triple=> [k ev|k _ ev|k ev].
- apply/restriction_loop=> // n' Pn'.
  by rewrite R // -renaming ev.
- apply/restriction_error=> // n' Pn'.
  by rewrite R // -renaming ev.
apply/restriction_ok=> // n' Pn'.
by rewrite R // [in RHS]R // -renaming ev.
Qed.

Definition eval_exprb e (s : state) : option value :=
  oexpose (mapb (fun s => eval_expr true s.1 e) s).

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
case ev_ex: eval_exprb=> [[b| | |]|] //.
apply: elim_triple_strong=> [k ev|k _ ev|k ev].
- exists k.+1=> /=; first exact: leqnSn.
  case: s / boundP ev ev_ex=> [/= A [ls h] sub].
  rewrite eval_exprbE bound_eval_condE /= => ev.
  by case: ifP=> _ // [->].
- exists k.+1=> /=.
  case: s / boundP ev ev_ex=> [/= A [ls h] sub].
  rewrite eval_exprbE bound_eval_condE /= => ev.
  by case: ifP=> _ // [->].
exists k.+1=> /=.
case: s / boundP ev ev_ex=> [/= A [ls h] sub].
rewrite eval_exprbE bound_eval_condE /= => ev.
by case: ifP=> _ // [->].
Qed.

Lemma triple_while e s ex c s' :
  match eval_exprb ex s with
  | Some (VBool b) => triple e s (if b then Seq c (While ex c) else Skip) s'
  | _ => False
  end ->
  triple e s (While ex c) s'.
Proof.
case ev_ex: eval_exprb=> [[b| | |]|] //.
apply: elim_triple_strong=> [k ev|k _ ev|k ev].
- exists k.+1=> /=; first exact: leqnSn.
  case: s / boundP ev ev_ex=> [/= A [ls h] sub].
  rewrite eval_exprbE bound_eval_condE /= => ev.
  by case: ifP=> _ // [->].
- exists k.+1=> /=.
  case: s / boundP ev ev_ex=> [/= A [ls h] sub].
  rewrite eval_exprbE bound_eval_condE /= => ev.
  by case: ifP=> _ // [->].
exists k.+1=> /=.
case: s / boundP ev ev_ex=> [/= A [ls h] sub].
rewrite eval_exprbE bound_eval_condE /= => ev.
by case: ifP=> _ // [->].
Qed.

Definition setl (s : state) x v :=
  locked mapb_fs _ _ (names v) (fun s => (setm s.1 x v, s.2)) s.

Lemma setlE A s x v :
  fsubset (names v) A ->
  fsubset A (names s) ->
  setl (mask A s) x v = mask A (setm s.1 x v, s.2).
Proof.
move=> sub1 sub2; rewrite /setl -lock /= mapb_fsE //.
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
rewrite /setl /locval -!lock /= mapb_fsE /=.
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
  triple No s (Assn x e) (setl s x v).
Proof.
move=> /= ev; exists 1=> /=; congr Done.
case: s / boundP ev => [/= A [ls h] sub].
rewrite eval_exprbE; case: ifP=> // sub' [ev].
move: sub'; rewrite bound_assnE /= ev => sub'.
by rewrite setlE //.
Qed.

Definition loadb (s : state) (ptr : name * int) :=
  odflt None (oexpose (locked mapb_fs _ _ (names ptr)
                              (fun s : locals * heap => s.2 ptr) s)).

Lemma loadbE A s ptr :
  fsubset (names ptr) A ->
  fsubset A (names s) ->
  loadb (mask A s) ptr =
  if fsubset (names (s.2 ptr)) A then
    s.2 ptr
  else None.
Proof.
move=> sub1 sub2; rewrite /loadb -lock mapb_fsE.
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
rewrite /loadb /blockat -!lock /= {1}/names /= /prod_names /= namesT fsetU0.
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

Lemma triple_load s x e ptr v :
  eval_exprb e s = Some (VPtr ptr) ->
  loadb s ptr = Some v ->
  triple No s (Load x e) (setl s x v).
Proof.
move=> /= ev_ex get; exists 1=> /=.
case: s / boundP ev_ex get => [/= A [ls h] sub].
rewrite eval_exprbE; case: ifP=> // sub' [ev].
rewrite ev in sub'; rewrite loadbE //=.
rewrite bound_loadE /= ev.
case: ifP=> // sub'' get; rewrite get /=; congr Done.
by rewrite get in sub''; rewrite setlE.
Qed.

Definition storeb (s : state) (ptr : name * int) v :=
  obound (locked mapb_fs _ _ (names ptr :|: names v)
                 (fun s => omap (fun h => (s.1, h)) (updm s.2 ptr v)) s).

Lemma storebE A s ptr v :
  fsubset (names ptr) A ->
  fsubset (names v) A ->
  fsubset A (names s) ->
  storeb (mask A s) ptr v =
  omap (fun h => mask A (s.1, h)) (updm s.2 ptr v).
Proof.
move: s ptr v => [/= ls h] ptr v sub1 sub2 sub3.
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
  triple No s (Store e e') s'.
Proof.
case: s / boundP=> [/= A [ls h] sub] ev_e ev_e' st.
exists 1=> /=; rewrite bound_storeE /=.
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
by rewrite /new -lock vars_s_hide vars_s_stateu vars_s_blockat IH fsetU0.
Qed.

Lemma pub_lb i vs : pub (lb i vs) = if vs is [::] then fset0 else fset1 i.
Proof.
elim: vs i=> //= [|v vs IH] i; first by rewrite pub_emp.
rewrite /new -lock pub_hide.
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
rewrite /new -lock.
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
rewrite /new -!lock /=.
move: (fresh _) (freshP A)=> n ninA /=.
rewrite rename_stateu rename_blockat renamesE /=.
by rewrite !rename_lh renamenE IH // fpermKV.
Qed.

Definition ll x vs : state :=
  new (names vs) (fun i => (x ::= lh i vs) * lb i vs).

Lemma ll0 x : ll x [::] = x ::= VNil.
Proof.
rewrite /ll /= -[RHS]stateus0 -[RHS]new_const namess0; congr new.
by rewrite stateus0 names_locval.
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
rewrite /ll namess1; apply/newP=> i Pn /=; rewrite namess1 new_stateur.
  rewrite names_locval namesvE /= !fsetU1E !fsetUA fsetUid.
  by apply/newP=> ??; rewrite stateuA.
move=> pm.
rewrite fsetU1E !fdisjointUr fdisjoints1 => /and3P [Pi Pv Pvs] i'.
rewrite !rename_stateu rename_lb rename_blockat /=.
rewrite {1}/rename /= names_disjointE // rename_lh names_disjointE //.
by rewrite -renamenE names_disjointE // namesnE fdisjoints1.
Qed.

Local Open Scope string_scope.

Local Notation "c1 ;; c2" :=
  (Seq c1 c2) (at level 70, right associativity).

Definition listrev :=
  While (Neg (Binop Eq (Var "x") ENil))
        (Load "y" (Binop Add (Var "x") (Num 1));;
         Store (Binop Add (Var "x") (Num 1)) (Var "r");;
         Assn "r" (Var "x");;
         Assn "x" (Var "y");;
         Assn "y" ENil).

Lemma listrev_spec vs :
  triple No
         (ll "x" vs * "r" ::= VNil * "y" ::= VNil)
         listrev
         ("x" ::= VNil * ll "r" (rev vs) * "y" ::= VNil).
Proof.
(*rewrite -(ll0 "r") -[rev vs]cats0.
elim: vs [::] => [|v vs IH] vs'.
  rewrite /rev /= !ll0 /listrev; apply: triple_while.
  admit.
rewrite rev_cons cat_rcons {1}/ll /=. -stateuA new_stateul; last first.
  move=> pm dis /= i; rewrite !rename_stateu rename_locval; congr stateu.
*)
admit.
Qed.

End Logic.
