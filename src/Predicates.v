(* Copyright (c) 2008-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import List.

Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Extra definitions to get coqdoc to choose the right fonts. *)

(* begin thide *)
Inductive unit := tt.
Inductive Empty_set := .
Inductive bool := true | false.
Inductive sum := .
Inductive prod := .
Inductive and := conj.
Inductive or := or_introl | or_intror.
Inductive ex := ex_intro.
Inductive eq := eq_refl.
Reset unit.
(* end thide *)
(* end hide *)

(**
(* %\chapter{Inductive Predicates}% *)
%\chapter{帰納的な述語}%
*)

(**
(* The so-called %\index{Curry-Howard correspondence}``%#"#Curry-Howard correspondence#"#%''~\cite{Curry,Howard}% states a formal connection between functional programs and mathematical proofs.  In the last chapter, we snuck in a first introduction to this subject in Coq.  Witness the close similarity between the types [unit] and [True] from the standard library: *)

関数プログラミングと数学の証明の間には%\index{Curry-Howard対応}``%#"#Curry-Howard対応#"#%''~\cite{Curry,Howard}%と呼ばれる形式的な関係があります。
実を言うとCoqにおけるCurry-Howard対応は前章ですでに初登場しています。
標準ライブラリの[unit]と[True]がとてもよく似ていることに注目してください。
<<
Print unit.
  Inductive unit : Set :=  tt : unit

Print True.
  Inductive True : Prop :=  I : True
>>
*)

(**
(* Recall that [unit] is the type with only one value, and [True] is the proposition that always holds.  Despite this superficial difference between the two concepts, in both cases we can use the same inductive definition mechanism.  The connection goes further than this.  We see that we arrive at the definition of [True] by replacing [unit] by [True], [tt] by [I], and [Set] by [Prop].  The first two of these differences are superficial changes of names, while the third difference is the crucial one for separating programs from proofs.  A term [T] of type [Set] is a type of programs, and a term of type [T] is a program.  A term [T] of type [Prop] is a logical proposition, and its proofs are of type [T].  Chapter 12 goes into more detail about the theoretical differences between [Prop] and [Set].  For now, we will simply follow common intuitions about what a proof is.

The type [unit] has one value, [tt].  The type [True] has one proof, [I].  Why distinguish between these two types?  Many people who have read about Curry-Howard in an abstract context but who have not put it to use in proof engineering answer that the two types in fact _should not_ be distinguished.  There is a certain aesthetic appeal to this point of view, but I want to argue that it is best to treat Curry-Howard very loosely in practical proving.  There are Coq-specific reasons for preferring the distinction, involving efficient compilation and avoidance of paradoxes in the presence of classical math, but I will argue that there is a more general principle that should lead us to avoid conflating programming and proving.

The essence of the argument is roughly this: to an engineer, not all functions of type [A -> B] are created equal, but all proofs of a proposition [P -> Q] are.  This idea is known as%\index{proof irrelevance}% _proof irrelevance_, and its formalizations in logics prevent us from distinguishing between alternate proofs of the same proposition.  Proof irrelevance is compatible with, but not derivable in, Gallina.  Apart from this theoretical concern, I will argue that it is most effective to do engineering with Coq by employing different techniques for programs versus proofs.  Most of this book is organized around that distinction, describing how to program, by applying standard functional programming techniques in the presence of dependent types; and how to prove, by writing custom Ltac decision procedures.

With that perspective in mind, this chapter is sort of a mirror image of the last chapter, introducing how to define predicates with inductive definitions.  We will point out similarities in places, but much of the effective Coq user's bag of tricks is disjoint for predicates versus "datatypes."  This chapter is also a covert introduction to dependent types, which are the foundation on which interesting inductive predicates are built, though we will rely on tactics to build dependently typed proof terms for us for now.  A future chapter introduces more manual application of dependent types. *)

[unit]は「ただ1つの値を持つ型」であり、[True]は「常に成り立つ命題」でした。
この2つの概念は、表面的には違いがありますが、いずれも同じ機構で帰納的に定義できています。
さらに[unit]と[True]の間には似ている面があります。
[unit]の定義中の[unit]を[True]に置き換え、[tt]を[I]に置き換え、[Set]を[Prop]に置き換えると、[True]の定義になることがわかります。
最初の2つの置き換えは名前の変更なのでさほど重要ではありません。それに対し3つめの置き換えは、プログラムと証明を分ける決定的な違いです。
[Set]型の[T]という項は、プログラムの集合を表す型であり、[T]型の項はプログラムです。
[Prop]型の[T]という項は、論理的な命題であり、その証明は[T]型を持ちます。
[Prop]と[Set]の理論的な違いは第12章でもっと詳細に説明しますが、今のところ「証明とは何か」については一般的な直観による理解に基づいて説明を続けます。

[unit]型は1つの値を持ち、それは[tt]です。
[True]型は1つの証明を持ち、それは[I]です。
これらの型を区別する理由はあるでしょうか？
多くの人は、カリーハワード対応を抽象的な説明として知っていて証明工学で使ったことがないうちは、これら2つの型を実際には区別する＿べきではない＿と考えます。
この見方には、ある種の審美的な魅力があります。しかし筆者の考えでは、実用的な証明においてはカリーハワード対応をゆるく活用して両者を区別するのが一番です。
両者を区別することには、Coq特有の理由、すなわち効率的なコンパイルと古典的な数学（論理学）におけるパラドクスを避けるためという理由もあります。
しかし、プログラミングと証明を混然一体にして扱うのを避けることは、むしろより一般的な原則から導かれる結論でもあるのです。

その原則とは何でしょうか。ごく大雑把に要約すると、「[A -> B]型の関数をすべて同じようにはプログラミングできないが、[P -> Q]という命題の証明はすべて同じようにできる」ということです。
この発想は%\index{proof irrelevance}%＿proof irrelevance＿として知られています。これを論理学で形式化すれば、同一の命題に対する異なる証明は互いに区別できない、ということが言えます。
このproof irrelevanceは、Gallina上で成立しますが、導出はできません。
本章では、この理論上の課題はいったんわきに置いておいて、proof irrelevanceがCoqにおける開発でとても効果的であり、そのおかげでプログラムと証明に対して別々の技法を使えることを見ていきます。
本書の大部分でも、プログラムを書く際には依存型のある関数プログラミングにおける標準的な技法を利用し、証明においてはLtacの決定手続きを独自に定義することで、両者の区別を利用しています。

上記のような観点に立てば、本章は前章の鏡像のようなものです。すなわち、本章では帰納的な定義を使って命題を定義する方法を紹介します。
命題は、随所で「データ型」との類似を指摘しているものの、その類似性がCoqを効果的に使うための道具になることはあまりありません。
さらに本章では依存型もこっそり導入します。依存型は面白い帰納的命題を作る土台です。
ただし依存型を使った証明項の構築では今のところタクティクを使い、手作業で依存型を活用する例は後の章で扱うことにします。
*)

(**
(* * Propositional Logic *)
* 命題論理
*)

(**
(* Let us begin with a brief tour through the definitions of the connectives for propositional logic.  We will work within a Coq section that provides us with a set of propositional variables.  In Coq parlance, these are just variables of type [Prop]. *)

命題論理で使われる結合記号の定義を簡単に見ていくことから始めましょう。
以降の説明はCoqのセクション内で進めます。セクション内では命題変数が使えます。
命題変数とは、Coqの用語で言えば、単なる[Prop]型の変数です。
*)

Section Propositional.
  Variables P Q R : Prop.

(**
(* In Coq, the most basic propositional connective is implication, written [->], which we have already used in almost every proof.  Rather than being defined inductively, implication is built into Coq as the function type constructor.

We have also already seen the definition of [True].  For a demonstration of a lower-level way of establishing proofs of inductive predicates, we turn to this trivial theorem. *)

Coqにおけるもっとも基本的な命題の結合記号は含意であり、[->]で表します。この記号は、これまでのほぼすべての証明でも使ってきました。
含意は帰納的に定義されているわけではなく、関数型の構成子としてCoqに組み込まれています。

帰納的な述語に対する証明を低レベルな方法で構成する例として、すでに定義を知っている[True]を使った次の自明な定理を見てみましょう。
*)
  
  Theorem obvious : True.
(* begin thide *)
    apply I.
(* end thide *)
  Qed.

(**
(* We may always use the [apply] tactic to take a proof step based on applying a particular constructor of the inductive predicate that we are trying to establish.  Sometimes there is only one constructor that could possibly apply, in which case a shortcut is available:%\index{tactics!constructor}% *)

証明のステップを進めるのに、証明を構成しようとしている帰納的な述語が持つ特定の構成子を適用する場合には、常に[apply]タクティクが使えます。
特に適用しうる構成子がただ1つしかない場合には、以下のように[constructor]というショートカット%\index{tactics!constructor}%が使えます。
*)

(* begin thide *)
  Theorem obvious' : True.
    constructor.
  Qed.

(* end thide *)

(**
(* There is also a predicate [False], which is the Curry-Howard mirror image of [Empty_set] from the last chapter. *)

[False]も述語です。これはカリーハワード対応では[Empty_set]の鏡像です。
<<
Print False.
  Inductive False : Prop :=
>>
*)

(**
(*  We can conclude anything from [False], doing case analysis on a proof of [False] in the same way we might do case analysis on, say, a natural number.  Since there are no cases to consider, any such case analysis succeeds immediately in proving the goal. *)

[False]からは、あらゆる結論を導けます。具体的には、自然数に対する場合分けと同じ要領で、[False]の証明に対して場合分けを行えばよいのです。
[False]の証明に対する場合分けでは考慮するケースがないので、即時にゴールの証明が成功します。
*)

  Theorem False_imp : False -> 2 + 2 = 5.
(* begin thide *)
    destruct 1.
(* end thide *)
  Qed.

(**
(* In a consistent context, we can never build a proof of [False].  In inconsistent contexts that appear in the courses of proofs, it is usually easiest to proceed by demonstrating the inconsistency with an explicit proof of [False]. *)

無矛盾のコンテキストからは[False]の証明を作れません。
証明の途中で矛盾したコンテキストが現れた場合には、[False]の証明を明示的に与えて矛盾を示すのが通常はもっとも簡単です。
*)

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
(* begin thide *)
    intro.

(**
(* At this point, we have an inconsistent hypothesis [2 + 2 = 5], so the specific conclusion is not important.  We use the %\index{tactics!elimtype}%[elimtype] tactic.  For a full description of it, see the Coq manual.  For our purposes, we only need the variant [elimtype False], which lets us replace any conclusion formula with [False], because any fact follows from an inconsistent context. *)

この時点で矛盾した仮定[2 + 2 = 5]があるので、特定の結論にはあまり意味がありません。
ここで利用するのは%\index{tactics!elimtype}%[elimtype]タクティクです（詳しい説明はCoqのマニュアルを参照）。
いまの目的では、単に[elimtype False]とすればよいでしょう。矛盾したコンテキストからは任意の事実が従うので、これにより結論がすべて[False]に置き換えられます。
*)

    elimtype False.


(** <<
  H : 2 + 2 = 5
  ============================
   False
>>

(* For now, we will leave the details of this proof about arithmetic to [crush]. *)
残りの算術に関する証明の詳細は[crush]しておきましょう。
*)

    crush.
(* end thide *)
  Qed.

(**
(* A related notion to [False] is logical negation. *)
[False]に関係する概念として論理否定があります。
*)

  (* begin hide *)
  Definition foo := not.
  (* end hide *)

(** <<
Print not.
  not = fun A : Prop => A -> False
      : Prop -> Prop
>>

(* We see that [not] is just shorthand for implication of [False].  We can use that fact explicitly in proofs.  The syntax [~ P] %(written with a tilde in ASCII)% expands to [not P].  *)

[not]は、上記からわかるように、「[False]への含意」の省略形にすぎません。
この事実を証明中で明示的に使うこともできます。
%(チルダ)%[~ P]という記法は[not P]に展開されます。
*)

  Theorem arith_neq' : ~ (2 + 2 = 5).
(* begin thide *)
    unfold not.
    crush.
(* end thide *)
  Qed.

(** <<
  ============================
   2 + 2 = 5 -> False
>>

(* We also have conjunction, which we introduced in the last chapter. *)

前章に出てきた連言もあります。
<<
  Print and.
    Inductive and (A : Prop) (B : Prop) : Prop :=  conj : A -> B -> A /\ B
>>

(*  The interested reader can check that [and] has a Curry-Howard equivalent called %\index{Gallina terms!prod}%[prod], the type of pairs.  However, it is generally most convenient to reason about conjunction using tactics.  An explicit proof of commutativity of [and] illustrates the usual suspects for such tasks.  The operator [/\] is an infix shorthand for [and]. *)

[and]は、カリーハワード対応によって%\index{Gallina terms!prod}%[prod]（ペアの型）と同値になります（興味がある読者は自分で確かめてみてください）。
ただし、連言に関する推論では一般にタクティクを使うのがもっとも簡便です。
そのことを示す好例として、[and]の可換性を明示的に証明してみましょう。
なお、[/\]演算子は[and]の中置による略記法です。
*)

  Theorem and_comm : P /\ Q -> Q /\ P.

(* begin thide *)
(**
(* We start by case analysis on the proof of [P /\ Q]. *)

[P /\ Q]の証明についての場合分けから始めます。
*)

    destruct 1.

(** <<
  H : P
  H0 : Q
  ============================
   Q /\ P
>>

(* Every proof of a conjunction provides proofs for both conjuncts, so we get a single subgoal reflecting that.  We can proceed by splitting this subgoal into a case for each conjunct of [Q /\ P].%\index{tactics!split}% *)

連言の証明では、常に両方の連言肢の証明をすることになります。上記で得られた唯一のサブゴール[Q /\ P]は、そのことを反映しています。
このサブゴールを分割して、[Q /\ P]のそれぞれの連言肢についての場合分けにより証明を進めることができます。
*)

    split.

(** <<
2 subgoals
  
  H : P
  H0 : Q
  ============================
   Q

subgoal 2 is

   P
>>

(* In each case, the conclusion is among our hypotheses, so the %\index{tactics!assumption}%[assumption] tactic finishes the process. *)
どちらの場合分けでも、結論が仮定に含まれているので、%\index{tactics!assumption}%[assumption]タクティクで証明を完了します。
*)

    assumption.
    assumption.
(* end thide *)
  Qed.

(**
(* Coq disjunction is called %\index{Gallina terms!or}%[or] and abbreviated with the infix operator [\/]. *)
選言は、Coqでは%\index{Gallina terms!or}%[or]を使います。略記として中置演算子[\/]が使えます。
<<
Print or.
  Inductive or (A : Prop) (B : Prop) : Prop :=
    or_introl : A -> A \/ B | or_intror : B -> A \/ B
>>
*)

(**
(* We see that there are two ways to prove a disjunction: prove the first disjunct or prove the second.  The Curry-Howard analogue of this is the Coq %\index{Gallina terms!sum}%[sum] type.  We can demonstrate the main tactics here with another proof of commutativity. *)

上記からわかるように、選言の証明には二つの方法があります。一つめの選言肢を証明するか、二つめの選言肢を証明するかです。
カリーハワード対応では、選言はCoqの[sum]型に対応します。
連言と同様、可換性の証明を例にして主なタクティクの使い方を見てみましょう。
*)

  Theorem or_comm : P \/ Q -> Q \/ P.

(* begin thide *)
(**
(* As in the proof for [and], we begin with case analysis, though this time we are met by two cases instead of one. *)

[and]の可換性を証明したときと同様、場合分けから始めます。ただし選言では場合分けが二通りあります。
*)

    destruct 1.

(** <<
2 subgoals
  
  H : P
  ============================
   Q \/ P

subgoal 2 is

 Q \/ P
>>

(**
(* We can see that, in the first subgoal, we want to prove the disjunction by proving its second disjunct.  The %\index{tactics!right}%[right] tactic telegraphs this intent. *)

最初のサブゴール[Q \/ P]については、右側にある選言肢の証明を与えることで、選言の証明としたいところです。
これには%\index{tactics!right}%[right]タクティクを使います。
*)

    right; assumption.
(**
(* The second subgoal has a symmetric proof.%\index{tactics!left}% *)

次のサブゴールの証明には、対称的な%\index{tactics!left}%[left]を使います。
<<
1 subgoal
  
  H : Q
  ============================
   Q \/ P
>>
*)

    left; assumption.

(* end thide *)
  Qed.


(* begin hide *)
(* In-class exercises *)

  Theorem contra : P -> ~P -> R.
(* begin thide *)
    unfold not.
    intros.
    elimtype False.
    apply H0.
    assumption.
(* end thide *)
  Admitted.

  Theorem and_assoc : (P /\ Q) /\ R -> P /\ (Q /\ R).
(* begin thide *)
    intros.
    destruct H.
    destruct H.
    split.
    assumption.
    split.
    assumption.
    assumption.
(* end thide *)
  Admitted.

  Theorem or_assoc : (P \/ Q) \/ R -> P \/ (Q \/ R).
(* begin thide *)
    intros.
    destruct H.
    destruct H.
    left.
    assumption.
    right.
    left.
    assumption.
    right.
    right.
    assumption.
(* end thide *)
  Admitted.

(* end hide *)

(**
(* It would be a shame to have to plod manually through all proofs about propositional logic.  Luckily, there is no need.  One of the most basic Coq automation tactics is %\index{tactics!tauto}%[tauto], which is a complete decision procedure for constructive propositional logic.  (More on what "constructive" means in the next section.)  We can use [tauto] to dispatch all of the purely propositional theorems we have proved so far. *)

命題論理の証明をすべて手作業でこつこつ進めるしかないとしたら大変です。
幸い、その必要はありません。
Coqには%\index{tactics!tauto}%[tauto]というタクティクが備わっています。
これは、構成的命題論理に対する完全な決定手続きであり、Coqに用意されている自動化のための基本的なタクティクのひとつです（ここで「構成的」が何を意味するかは次節で説明します）。
ここまで証明してきた純粋な命題論理の定理はすべて[tauto]に任せることができます。
*)

  Theorem or_comm' : P \/ Q -> Q \/ P.
(* begin thide *)
    tauto.
(* end thide *)
  Qed.

(**
(* Sometimes propositional reasoning forms important plumbing for the proof of a theorem, but we still need to apply some other smarts about, say, arithmetic.  The tactic %\index{tactics!intuition}%[intuition] is a generalization of [tauto] that proves everything it can using propositional reasoning.  When some further facts must be established to finish the proof, [intuition] uses propositional laws to simplify them as far as possible.  Consider this example, which uses the list concatenation operator %\coqdocnotation{%#<tt>#++#</tt>#%}% from the standard library. *)

命題論理による推論は、定理の証明を組み立てる際の重要な部品になることもありますが、それだけでは足りません。
算術のような他の知恵を使う必要もあります。
Coqには、%\index{tactics!intuition}%[intuition]という、汎用の[tauto]として使えるタクティクがあります。
[intuition]を使うことで、命題論理による推論を使って証明できるものは何でも証明できます。
さらに[intuition]は、証明を完了するために確立すべき事実がほかにあるときは、命題論理の法則を使ってそれをなるべく簡潔な形にしてくれます。
標準ライブラリのリスト連結演算%\coqdocnotation{%#<tt>#++#</tt>#%}%を使っている下記の例を考えてみましょう。
*)

  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
(* begin thide *)
    intuition.

(**
(* A lot of the proof structure has been generated for us by [intuition], but the final proof depends on a fact about lists.  The remaining subgoal hints at what cleverness we need to inject. *)

最終的な証明はリストに関する事実に依存しますが、証明の構造の大部分は[intuition]が生成してくれます。
その上で残されているサブゴールを見れば、人間が知恵をしぼって手を入れる必要があるもの何であるかヒントが見えてきます。
<<
  ls1 : list nat
  ls2 : list nat
  H0 : length ls1 + length ls2 = 6
  ============================
   length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2
>>

(**
(* We can see that we need a theorem about lengths of concatenated lists, which we proved last chapter and is also in the standard library. *)
このサブゴールを見ると、必要なのは連結したリストの長さに関する定理であることがわかります。前章でも証明した定理ですが、標準ライブラリにも[app_length]として含まれています。
*)

    rewrite app_length.

(** <<
  ls1 : list nat
  ls2 : list nat
  H0 : length ls1 + length ls2 = 6
  ============================
   length ls1 + length ls2 = 6 \/ length ls1 = length ls2
>>

(**
(* Now the subgoal follows by purely propositional reasoning.  That is, we could replace [length ls1 + length ls2 = 6] with [P] and [length ls1 = length ls2] with [Q] and arrive at a tautology of propositional logic. *)
ここまでくれば、純粋に命題論理の推論によってサブゴールを証明できます。
すなわち、[length ls1 + length ls2 = 6]を[P]に置き換え、[length ls1 = length ls2]を[Q]に置き換えれば、これは純粋な命題論理なので、[tauto]で証明できます。
*)

    tauto.
(* end thide *)
  Qed.

(**
(* The [intuition] tactic is one of the main bits of glue in the implementation of [crush], so, with a little help, we can get a short automated proof of the theorem. *)

[crush]の実装では、接着剤として[intuition]タクティクも使われています。
そのため、少しヒントを与えることで、定理に対する短くて自動化された証明が得られます。
*)

(* begin thide *)
  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.

    crush.
  Qed.
(* end thide *)

End Propositional.

(**
(* Ending the section here has the same effect as always.  Each of our propositional theorems becomes universally quantified over the propositional variables that we used. *)

ここでセクションを終了したので、本節で証明した命題論理の各定理は、いずれも証明中で利用した命題変数上で普遍的に限量化されたものになります。
*)

(**
(* * What Does It Mean to Be Constructive? *)
* 構成的であるとは何を意味するか
*)

(**
(* One potential point of confusion in the presentation so far is the distinction between [bool] and [Prop].  The datatype [bool] is built from two values [true] and [false], while [Prop] is a more primitive type that includes among its members [True] and [False].  Why not collapse these two concepts into one, and why must there be more than two states of mathematical truth, [True] and [False]?

The answer comes from the fact that Coq implements%\index{constructive logic}% _constructive_ or%\index{intuitionistic logic|see{constructive logic}}% _intuitionistic_ logic, in contrast to the%\index{classical logic}% _classical_ logic that you may be more familiar with.  In constructive logic, classical tautologies like [~ ~ P -> P] and [P \/ ~ P] do not always hold.  In general, we can only prove these tautologies when [P] is%\index{decidability}% _decidable_, in the sense of %\index{computability|see{decidability}}%computability theory.  The Curry-Howard encoding that Coq uses for [or] allows us to extract either a proof of [P] or a proof of [~ P] from any proof of [P \/ ~ P].  Since our proofs are just functional programs which we can run, a general %\index{law of the excluded middle}%law of the excluded middle would give us a decision procedure for the halting problem, where the instantiations of [P] would be formulas like "this particular Turing machine halts."

A similar paradoxical situation would result if every proposition evaluated to either [True] or [False].  Evaluation in Coq is decidable, so we would be limiting ourselves to decidable propositions only.

Hence the distinction between [bool] and [Prop].  Programs of type [bool] are computational by construction; we can always run them to determine their results.  Many [Prop]s are undecidable, and so we can write more expressive formulas with [Prop]s than with [bool]s, but the inevitable consequence is that we cannot simply "run a [Prop] to determine its truth."

Constructive logic lets us define all of the logical connectives in an aesthetically appealing way, with orthogonal inductive definitions.  That is, each connective is defined independently using a simple, shared mechanism.  Constructivity also enables a trick called%\index{program extraction}% _program extraction_, where we write programs by phrasing them as theorems to be proved.  Since our proofs are just functional programs, we can extract executable programs from our final proofs, which we could not do as naturally with classical proofs.

We will see more about Coq's program extraction facility in a later chapter.  However, I think it is worth interjecting another warning at this point, following up on the prior warning about taking the Curry-Howard correspondence too literally.  It is possible to write programs by theorem-proving methods in Coq, but hardly anyone does it.  It is almost always most useful to maintain the distinction between programs and proofs.  If you write a program by proving a theorem, you are likely to run into algorithmic inefficiencies that you introduced in your proof to make it easier to prove.  It is a shame to have to worry about such situations while proving tricky theorems, and it is a happy state of affairs that you almost certainly will not need to, with the ideal of extracting programs from proofs being confined mostly to theoretical studies. *)

ここまでの例を通して、[bool]と[Prop]が区別されていることに混乱している方がいるかもしれません。
[bool]というデータ型は、[true]と[false]という二つの値から構成されています。一方の[Prop]は、[True]と[False]を要素として含む、より原始的な型です。
これらの概念を集約せず、[True]と[False]の二つ以外に数学的な真偽の状態を必要としていることには、何か理由があるのでしょうか？

その答えは、Coqが実装しているのがお馴染みの%\index{古典論理}%古典論理ではなく、%\index{構成的論理}%＿構成的論理＿、あるいは%\index{直観主義論理|see{構成的論理}}%＿直観主義論理＿だからです。
構成的論理では、[~ ~ P -> P]や[P \/ ~ P]のような、古典論理では恒真な命題が常には成り立ちません。
これらの恒真な命題を証明できるのは、%\index{計算可能性理論|see{決定可能性}}%計算可能性理論で言うところの、[P]が%\index{決定可能性}%＿決定可能＿な場合のみです。
Coqにおける[or]のカリーハワード対応は、[P \/ ~ P]の任意の証明から[P]の証明もしくは[~ P]の証明を抽出することを許しています。
Coqにおける証明は実行可能な関数プログラムにすぎないので、もし%\index{排中律}%排中律を許せば、[P]の具体化として「このチューリングマシンは停止する」のような式を選ぶことで、停止問題に対する決定手続きが得られてしまいます。

「すべての命題が[True]または[False]に評価される」とすることには、同様のパラドクスを引き起こす恐れがあります。
Coqにおけるプログラムの評価は決定可能なので、扱う命題も決定可能なものに限ることにします。

[bool]と[Prop]が区別されているのは、こうした理由によります。[bool]型のプログラムは、その構成からして計算を扱うものであり、常に実行することで決定可能です。
[Prop]には決定不能なものも多くあるので、[bool]を使っては表現できない式が書けるようになりますが、必然的に「真偽を確かめるために[Prop]を実行する」ことはできません。

構成的論理を採用すると、どの論理結合も直交した帰納的定義によるすっきりした方法で定義できるようになります。
言い換えると、個々の論理結合を簡潔かつ共通の機構で独立に定義できます。
また、構成的論理には%\index{program extraction}%プログラム抽出が可能になるという特長もあります。
これは、プログラムを「証明すべき定理」として記述できるということです。
Coqにおける証明は単なる関数プログラムなので、証明ができれば、そこから実行できるプログラムを抽出できます。これは古典論理では自然に実現できなかったでしょう。

Coqのプログラム抽出機能については後の章でより詳しく説明しますが、ここでも改めて注意しておきます。
あまりカリーハワード対応を真に受けないでください。
Coqによる定理証明を使ってプログラムを書くことは可能ですが、実際にやる人はほとんどいません。
証明とプログラムは常に区別するように心がけてください。
定理を証明することでプログラムを書けば、証明を簡単にしようとする努力の結果、アルゴリズムの面での非効率に悩まされることでしょう。
ややこしい定理を証明してる最中にそのような側面を考慮するのはまず無理です。
もっとも、証明からプログラムを抽出するという究極の目標はほとんど理論的な研究の分野に限定されているので、通常はそのような心配は不要なはずです。
*)

(** 
(* * First-Order Logic *)
* 一階の論理
*)

(** 
(* The %\index{Gallina terms!forall}%[forall] connective of first-order logic, which we have seen in many examples so far, is built into Coq.  Getting ahead of ourselves a bit, we can see it as the dependent function type constructor.  In fact, implication and universal quantification are just different syntactic shorthands for the same Coq mechanism.  A formula [P -> Q] is equivalent to [forall x : P, Q], where [x] does not appear in [Q].  That is, the "real" type of the implication says "for every proof of [P], there exists a proof of [Q]."

%\index{existential quantification}\index{Gallina terms!exists}\index{Gallina terms!ex}%Existential quantification is defined in the standard library. *)

これまでの例にも登場しているように、Coqには一階の論理における%\index{Gallina terms!forall}%[forall]限定子が組み込まれています。
[forall]結合子は、少し先取りして言うと、依存関数型の構成子とみなせます。
実際、含意と全称限量化は、Coqでは同一の機構に対する別々の記法にすぎません。
[P -> Q]という式は[forall x : P, Q]と等価なのです（ただし[x]は[Q]には現れないものとします）。
言い換えると、含意には「[P]のすべての証明に対し、[Q]の証明が存在する」という意味合いになります。

%\index{existential quantification}\index{Gallina terms!exists}\index{Gallina terms!ex}%
存在限量化は標準ライブラリで次のように定義されています。
<<
  Print ex.
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P
>>

(*  (Note that here, as always, each [forall] quantifier has the largest possible scope, so that the type of [ex_intro] could also be written [forall x : A, (P x -> ex P)].)

  The family [ex] is parameterized by the type [A] that we quantify over, and by a predicate [P] over [A]s.  We prove an existential by exhibiting some [x] of type [A], along with a proof of [P x].  As usual, there are tactics that save us from worrying about the low-level details most of the time.

  Here is an example of a theorem statement with existential quantification.  We use the equality operator [=], which, depending on the settings in which they learned logic, different people will say either is or is not part of first-order logic.  For our purposes, it is. *)

（[forall]限定子のスコープは常にできるだけ大きく取られるので、上記の[ex_intro]は[forall x : A, (P x -> ex P)]とも書いたのと同じです。）

[ex]は、限量化する型[A]と、[A]上の術語[P]をパラーメータとして取ります。
存在限量化された命題の証明では、型[A]を持つ何らかの[x]を、[P x]の証明を添えて提示することになります。
他の証明と同様、低レベルな細部に煩わされる時間はタクティクを使うことで節約できます。

存在限量子を含む定理の例を以下に示します。
等価性の演算子[=]については、どこで論理学を勉強したかによって一階の論理に含まれるか否かで意見が分かれるところですが、ここでは含まれるものとします。

*)

Theorem exist1 : exists x : nat, x + 1 = 2.
(* begin thide *)

(* remove printing exists *)

(**
(* We can start this proof with a tactic %\index{tactics!exists}%[exists], which should not be confused with the formula constructor shorthand of the same name.  %In the version of this document that you are reading, the reverse ``E'' appears instead of the text ``exists'' in formulas.% *)

上記の式に出てくる「逆向きのE」は存在限量子の構成子であり、Coqにおける入力では「exists」というASCIIの文字列です。
この定理は、次のように%\index{tactics!exists}%[exists]タクティク（構成子と同名ですが混同しないように注意してください）を使って証明を開始できます。
*)

  exists 1.

(** 
(* The conclusion is replaced with a version using the existential witness that we announced. *)

これにより、[exists]タクティクで伝えた存在証明によって置き換えられた結果が得られます。
<<
  ============================
   1 + 1 = 2
>>
*)

  reflexivity.
(* end thide *)
Qed.

(* printing exists $\exists$ *)

(**
(* We can also use tactics to reason about existential hypotheses. *)
存在限量化を仮定に含む推論でもタクティクが使えます。
*)

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.

(**
(* begin thide *)
  (* We start by case analysis on the proof of the existential fact. *)
  存在についての事実を場合分けで証明しましょう。
*)

  destruct 1.
  
(** <<
  n : nat
  m : nat
  x : nat
  H : n + x = m
  ============================
   n <= m
>>

(*   The goal has been replaced by a form where there is a new free variable [x], and where we have a new hypothesis that the body of the existential holds with [x] substituted for the old bound variable.  From here, the proof is just about arithmetic and is easy to automate. *)

ゴールが置き換えられて、新たな自由変数[x]と、「その新しい自由変数[x]で元の束縛変数[x]を置き換えた式」を新たな仮定とするフォームが得られました。
あとは算術に関する証明だけなので自動でできます。
*)

  crush.
(* end thide *)
Qed.


(* begin hide *)
(* In-class exercises *)

Theorem forall_exists_commute : forall (A B : Type) (P : A -> B -> Prop),
  (exists x : A, forall y : B, P x y) -> (forall y : B, exists x : A, P x y).
(* begin thide *)
  intros.
  destruct H.
  exists x.
  apply H.
(* end thide *)
Admitted.

(* end hide *)


(**
(* The tactic [intuition] has a first-order cousin called %\index{tactics!firstorder}%[firstorder], which proves many formulas when only first-order reasoning is needed, and it tries to perform first-order simplifications in any case.  First-order reasoning is much harder than propositional reasoning, so [firstorder] is much more likely than [intuition] to get stuck in a way that makes it run for long enough to be useless. *)

一階の論理にも[intuition]タクティクに相当するものがあります。
%\index{tactics!firstorder}%[firstorder]タクティクです。
このタクティクにより、一階の論理による推論のみを必要とする式の多くが証明できます。
また、多くの場合には、一階の論理を使った簡約も実施してくれます。
一階の論理による推論は命題論理による推論よりも難しいので、[firstorder]は[intuition]よりもスタックしがちです。
そのため、使いものにならないと判明するまで長い時間を無駄にすることもよくあります。
*)

(**
(* * Predicates with Implicit Equality *)
* 暗黙の等価性を持つ命題

(* We start our exploration of a more complicated class of predicates with a simple example: an alternative way of characterizing when a natural number is zero. *)

もう少し複雑なクラスの命題も見ていきましょう。
最初の簡単な例は、ある自然数がゼロであることを言う別の方法です。

*)

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
(* begin thide *)
  constructor.
(* end thide *)
Qed.

(**
(* We can call [isZero] a%\index{judgment}% _judgment_, in the sense often used in the semantics of programming languages.  Judgments are typically defined in the style of%\index{natural deduction}% _natural deduction_, where we write a number of%\index{inference rules}% _inference rules_ with premises appearing above a solid line and a conclusion appearing below the line.  In this example, the sole constructor [IsZero] of [isZero] can be thought of as the single inference rule for deducing [isZero], with nothing above the line and [isZero 0] below it.  The proof of [isZero_zero] demonstrates how we can apply an inference rule.  (Readers not familiar with formal semantics should not worry about not following this paragraph!) *)

プログラミング言語の意味論では_判断_（%\index{judgment}%_judgment_）という概念がよく出てきます。
上記の[isZero]は、この意味での「判断」だと言えます。
判断は、%\index{自然演繹}% _自然演繹_と同じスタイルで、「上に前提、下に結論を配した横線を伴う、複数の%\index{導出規則}% _導出規則_（inference rule）」として示されるのが一般的です。
上記の例では、[isZero]の構成子は[IsZero]だけであり、これが[isZero]の唯一の導出規則とみなせます。
この場合、横線の上には何も配置されず、下には[isZero 0]だけが配置されます。
[isZero_zero]の証明を見れば、導出規則の適用方法がわかるでしょう。
（形式的意味論に不慣れな読者は、この段落の説明は読み飛ばしてもかまいません。）

(* The definition of [isZero] differs in an important way from all of the other inductive definitions that we have seen in this and the previous chapter.  Instead of writing just [Set] or [Prop] after the colon, here we write [nat -> Prop].  We saw examples of parameterized types like [list], but there the parameters appeared with names _before_ the colon.  Every constructor of a parameterized inductive type must have a range type that uses the same parameter, whereas the form we use here enables us to choose different arguments to the type for different constructors. *)

[isZero]の定義は、ある重要な点で、前章と本章でこれまでに見た帰納的定義とは異なります。
コロンの直後に、[Set]や[Prop]ではなく、[nat -> Prop]と書いている点です。
パラメータ付きの型は、これまでにも[list]などで登場していますが、そこではパラメータが名前と一緒にコロンの_前_に置かれていました。
パラメータ付きの帰納型の各構成子には、それぞれ範囲のある型を持たせる必要があり、それらは同じパラメータを使うのですが、上記の例では個々の構成子に対し別々の変数を型として指定するような書き方をしています。

(* For instance, our definition [isZero] makes the predicate provable only when the argument is [0].  We can see that the concept of equality is somehow implicit in the inductive definition mechanism.  The way this is accomplished is similar to the way that logic variables are used in %\index{Prolog}%Prolog (but worry not if not familiar with Prolog), and it is a very powerful mechanism that forms a foundation for formalizing all of mathematics.  In fact, though it is natural to think of inductive types as folding in the functionality of equality, in Coq, the true situation is reversed, with equality defined as just another inductive type!%\index{Gallina terms!eq}\index{Gallina terms!refl\_equal}% *)

上記の[isZero]の定義により命題を証明できるのは、引数が[0]の場合だけです。
このことからは、帰納的な定義の背後に等価性の概念が暗黙にあることがわかります。
%\index{Prolog}%Prologを知っている人には、論理変数のユニフィケーションに似た仕組みだと言えば伝わると思います。
この仕組みは、あらゆる数学を定式化するための基盤を作る上で、実に強力です。
帰納型は、等価性を織り込んだ機能としてとらえるのが自然だと言えるでしょう。
ただし、実を言うとCoqでは話が逆で、等価性が帰納型のひとつとして次のように定義されています%\index{Gallina terms!eq}\index{Gallina terms!refl\_equal}%。
<<<
Print eq.
  Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x
>>>

(*  Behind the scenes, uses of infix [=] are expanded to instances of [eq].  We see that [eq] has both a parameter [x] that is fixed and an extra unnamed argument of the same type.  The type of [eq] allows us to state any equalities, even those that are provably false.  However, examining the type of equality's sole constructor [eq_refl], we see that we can only _prove_ equality when its two arguments are syntactically equal.  This definition turns out to capture all of the basic properties of equality, and the equality-manipulating tactics that we have seen so far, like [reflexivity] and [rewrite], are implemented treating [eq] as just another inductive type with a well-chosen definition.  Another way of stating that definition is: equality is defined as the least reflexive relation.*)

中置記法[=]は、裏では[eq]のインスタンスへと展開されます。
[eq]は、[x]という固定のパラメータと、同じ型で無名の追加の引数を取るものと理解でき、その型のおかげであらゆる等価性（偽になりうるものを含め）を表現できるようになっています。
ただし、等価性の型の[eq_refl]という唯一の構成子をよく見るとわかりますが、等価であることを_証明_できるのは[eeq]の2つの引数が記法の上で同一である場合だけです。
この定義は等価性の基本的な性質をすべて捉えたものになっています。
実際、ここまでに登場した[reflexivity]や[rewrite]のような等価性を扱うタクティクの実装では、[eq]を単なる「うまく定義が選ばれた帰納型」として扱っています。
上記の[eq]の定義は、「等価性は最小の反射的な関係として定義されている」と言い表してもいいでしょう。

(* Returning to the example of [isZero], we can see how to work with hypotheses that use this predicate. *)

話を[isZero]の例に戻します。この命題が仮定に使われている定理を証明してみましょう。
*)

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
(* begin thide *)
  (** 
    (* We want to proceed by cases on the proof of the assumption about [isZero]. *)
    [isZero]が出てくる仮定について、場合分けをします。 *)

  destruct 1.
(** <<
  n : nat
  ============================
   n + 0 = n
>>

(*   Since [isZero] has only one constructor, we are presented with only one subgoal.  The argument [m] to [isZero] is replaced with that type's argument from the single constructor [IsZero].  From this point, the proof is trivial. *)

[isZero]の構成子は一つだけなので、サブゴールも一つだけです。
[isZero]の引数である[m]が、その型の唯一の構成子[IsZero]の引数で置き換えられています。
ここまでくれば証明は自明です。
*)

  crush.
(* end thide *)
Qed.

(**
(* Another example seems at first like it should admit an analogous proof, but in fact provides a demonstration of one of the most basic gotchas of Coq proving. *)

次は、先の例と大差ないものに見えるかもしれませんが、実はCoqにおける証明でもっとも基本的な勘所のひとつを示す例です。
*)

Theorem isZero_contra : isZero 1 -> False.
(* begin thide *)
  (**
   (* Let us try a proof by cases on the assumption, as in the last proof. *)
   前と同じように仮定に関する場合分けで証明してみましょう。 *)
  
  destruct 1.

(** <<
  ============================
   False
>>

(*   It seems that case analysis has not helped us much at all!  Our sole hypothesis disappears, leaving us, if anything, worse off than we were before.  What went wrong?  We have met an important restriction in tactics like [destruct] and [induction] when applied to types with arguments.  If the arguments are not already free variables, they will be replaced by new free variables internally before doing the case analysis or induction.  Since the argument [1] to [isZero] is replaced by a fresh variable, we lose the crucial fact that it is not equal to [0]. *)

どうやら場合分けではうまくいかないようです。
たった一つしかない仮定が消えてしまい、最初の時点よりゴールから遠ざかってしまいました。
何がまずかったのでしょうか。
[destruct]や[induction]のようなタクティクには、引数を持つ型に適用する場合には重要な制限があり、それに抵触したのです。
引数は、すでに自由変数になっているのでなければ、[destruct]や[induction]が実行される前に内部で新しい自由変数に置き換えられます。
[isZero]に対する引数[1]が新しい自由変数に置き換えられた結果、これが[0]ではないという決定的な事実が失われてしまったのです。

(*   Why does Coq use this restriction?  We will discuss the issue in detail in a future chapter, when we see the dependently typed programming techniques that would allow us to write this proof term manually.  For now, we just say that the algorithmic problem of "logically complete case analysis" is undecidable when phrased in Coq's logic.  A few tactics and design patterns that we will present in this chapter suffice in almost all cases.  For the current example, what we want is a tactic called %\index{tactics!inversion}%[inversion], which corresponds to the concept of inversion that is frequently used with natural deduction proof systems.  (Again, worry not if the semantics-oriented terminology from this last sentence is unfamiliar.) *)

なぜCoqにはこのような制限があるのでしょうか。
詳しいことは、依存型のプログラミングの技法を使って証明項を手作業で書くことを説明する章で議論します。
今のところは、「論理的に完全な場合分け」にはアルゴリズム上の問題があってCoqの論理では決定不能である、とだけ言っておきます。
ほとんどの場合、本章に登場するいくつかのタクティクとデザインパターンで困ることはありません。
この例で必要なのは、%\index{tactics!inversion}%[inversion]というタクティクです。
このタクティクは、自然演繹の証明システムでよく使われる「逆転」（inversion）という概念に対応しています。
*)

  Undo.
  inversion 1.
(* end thide *)
Qed.

(** 
(* What does [inversion] do?  Think of it as a version of [destruct] that does its best to take advantage of the structure of arguments to inductive types.  In this case, [inversion] completed the proof immediately, because it was able to detect that we were using [isZero] with an impossible argument.*)

[inversion]は何をするタクティクなのでしょうか。
「帰納型の引数の構造をできるだけ利用してくれる[destruct]の亜種」だと思うのが一番わかりやすいでしょう。
この例では、[isZero]にありえない引数が使われていることを[inversion]が見つけてくれるので、たちどころに証明が終わります。

(* Sometimes using [destruct] when you should have used [inversion] can lead to confusing results.  To illustrate, consider an alternate proof attempt for the last theorem. *)

[inversion]を使うべき場面で[destruct]を使うと、思いがけない結果が得られて混乱することもあります。
例として、先の定理の結論を別の矛盾した式に置き換えたものを証明してみましょう。
*)

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
  (** <<
  ============================
   1 + 1 = 4
   >>
   
(*   What on earth happened here?  Internally, [destruct] replaced [1] with a fresh variable, and, trying to be helpful, it also replaced the occurrence of [1] within the unary representation of each number in the goal.  Then, within the [O] case of the proof, we replace the fresh variable with [O].  This has the net effect of decrementing each of these numbers. *)

何が起こったのでしょうか。
[destruct]は、内部で[1]を新しい自由変数に置き換え、さらにゴールの各数字の単項表現に出現する[1]も置き換えようとします。
その後、証明における場合分けに際し、[0]の場合には新しい自由変数が[0]で置き換えられます。
この合わせ技で各数字が1ずつ減算されるのです。
*)

Abort.

(**
(* To see more clearly what is happening, we can consider the type of [isZero]'s induction principle. *)

[isZero]の型について帰納法の原理を確認してみると、より明確に何が起きているかわかります。
<<
Check isZero_ind.
isZero_ind
     : forall P : nat -> Prop, P 0 -> forall n : nat, isZero n -> P n
>>

(*   In our last proof script, [destruct] chose to instantiate [P] as [fun n => S n + S n = S (S (S (S n)))].  You can verify for yourself that this specialization of the principle applies to the goal and that the hypothesis [P 0] then matches the subgoal we saw generated.  If you are doing a proof and encounter a strange transmutation like this, there is a good chance that you should go back and replace a use of [destruct] with [inversion]. *)

先の証明では、[destruct]により、[P]が[fun n => S n + S n = S (S (S (S n)))]のように具体化されます。
自分で確かめてみれば、帰納法の原理によるこの特定化をゴールに適用できて、[P 0]という仮定が先の例で得られたサブゴールに合致することが確認できるでしょう。
証明をしていて奇妙な変身に遭遇した場合には、[destruct]の代わりに[inversion]を使ってみるとうまくいくかもしれません。
*)

(* begin hide *)
(* In-class exercises *)

(* EX: Define an inductive type capturing when a list has exactly two elements.  Prove that your predicate does not hold of the empty list, and prove that, whenever it holds of a list, the length of that list is two. *)

(* begin thide *)
Section twoEls.
  Variable A : Type.

  Inductive twoEls : list A -> Prop :=
  | TwoEls : forall x y, twoEls (x :: y :: nil).

  Theorem twoEls_nil : twoEls nil -> False.
    inversion 1.
  Qed.

  Theorem twoEls_two : forall ls, twoEls ls -> length ls = 2.
    inversion 1.
    reflexivity.
  Qed.
End twoEls.
(* end thide *)

(* end hide *)


(** (* Recursive Predicates *)
* 再帰的な命題
*)

(**
(* We have already seen all of the ingredients we need to build interesting recursive predicates, like this predicate capturing even-ness. *)

ここまでの説明で、興味深い再帰的な命題の構築に必要な要素はすべて登場しました。
例として次のような偶奇性に関する命題を見てみましょう。
*)

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

(** 

(* Think of [even] as another judgment defined by natural deduction rules.  The rule [EvenO] has nothing above the line and [even O] below the line, and [EvenSS] is a rule with [even n] above the line and [even (S (S n))] below. *)

[even]もまた、自然演繹の規則によって定義されており、判断だと考えられます。
規則[EvenO]は、横線の上には何もなく、下には[even O]がある規則です。
[EvenSS]は、横線の上に[even n]があり、下には[even (S (S n))]がある規則です。

(* The proof techniques of the last section are easily adapted. *)

前節の技法をそのまま使うのは簡単です。
*)

Theorem even_0 : even 0.
(* begin thide *)
  constructor.
(* end thide *)
Qed.

Theorem even_4 : even 4.
(* begin thide *)
  constructor; constructor; constructor.
(* end thide *)
Qed.

(** 

(* It is not hard to see that sequences of constructor applications like the above can get tedious.  We can avoid them using Coq's hint facility, with a new [Hint] variant that asks to consider all constructors of an inductive type during proof search.  The tactic %\index{tactics!auto}%[auto] performs exhaustive proof search up to a fixed depth, considering only the proof steps we have registered as hints. *)

このように構成子の適用を並べていく方法が冗長であることは想像に難くないでしょう。
これはCoqが備えるヒントの仕組みを使えば回避できます。
具体的には、帰納型のすべての構成子を証明の探索にあたって考慮するように、[Hint]というヴァリアントを使って指定します。
これにより、%\index{tactics!auto}%[auto]タクティクで一定の深さまで証明を全探索する際、ヒントとして登録した証明のステップのみが考慮されるようになります。

*)
 
(* begin thide *)
Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

(* end thide *)

(**
(* We may also use [inversion] with [even]. *)

[even]を使った定理を[inversion]で証明することもできます。
*)

Theorem even_1_contra : even 1 -> False.
(* begin thide *)
  inversion 1.
(* end thide *)
Qed.

Theorem even_3_contra : even 3 -> False.
(* begin thide *)
  inversion 1.
  (** <<
  H : even 3
  n : nat
  H1 : even 1
  H0 : n = 1
  ============================
   False
  >>

(*   The [inversion] tactic can be a little overzealous at times, as we can see here with the introduction of the unused variable [n] and an equality hypothesis about it.  For more complicated predicates, though, adding such assumptions is critical to dealing with the undecidability of general inversion.  More complex inductive definitions and theorems can cause [inversion] to generate equalities where neither side is a variable. *)

[inversion]タクティクは、少し余計なことをする場合があって、上記の例では使用していない変数[n]とその変数に関する等価性についての仮定が導入されています。
とはいえ、こうした仮定の追加は、一般的な逆転における非決定性への対処のために、より複雑な命題では不可欠なものです。
帰納的な定義と定理が複雑になると、[inversion]によって左右のいずれも変数になっていない等式が生成される場合があるのです。
*)

  inversion H1.
(* end thide *)
Qed.

(**
(* We can also do inductive proofs about [even]. *)

[even]についての帰納的な証明も可能です。
*)

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
(* begin thide *)
  (**
  (* It seems a reasonable first choice to proceed by induction on [n]. *)
  一見すると[n]についての帰納法で進めるのがよさそうに思えます。
  *)
  
  induction n; crush.
  (** <<
  n : nat
  IHn : forall m : nat, even n -> even m -> even (n + m)
  m : nat
  H : even (S n)
  H0 : even m
  ============================
   even (S (n + m))
  >>

  (* We will need to use the hypotheses [H] and [H0] somehow.  The most natural choice is to invert [H]. *)
  
  なんとかして仮定[H]と[H0]を使う必要があります。
  [H]を逆転させるのが自然でしょう。
  *)

  inversion H.
  (** <<
  n : nat
  IHn : forall m : nat, even n -> even m -> even (n + m)
  m : nat
  H : even (S n)
  H0 : even m
  n0 : nat
  H2 : even n0
  H1 : S n0 = n
  ============================
   even (S (S n0 + m))
  >>

  (* Simplifying the conclusion brings us to a point where we can apply a constructor. *)
  
  結論を簡約すると、構成子を適用できるようになります。
  *)

  simpl.
  (** <<
  ============================
   even (S (S (n0 + m)))
  >>
  *)

  constructor.

(** <<
  ============================
   even (n0 + m)
   >>

  (* At this point, we would like to apply the inductive hypothesis, which is: *)

  この段階で以下のような帰納法の仮定を使いたくなるところです。
  <<
  IHn : forall m : nat, even n -> even m -> even (n + m)
  >>

  (* Unfortunately, the goal mentions [n0] where it would need to mention [n] to match [IHn].  We could keep looking for a way to finish this proof from here, but it turns out that we can make our lives much easier by changing our basic strategy.  Instead of inducting on the structure of [n], we should induct _on the structure of one of the [even] proofs_.  This technique is commonly called%\index{rule induction}% _rule induction_ in programming language semantics.  In the setting of Coq, we have already seen how predicates are defined using the same inductive type mechanism as datatypes, so the fundamental unity of rule induction with "normal" induction is apparent. *)
  
  残念ながら、[IHn]に合致する[n]が必要なところで、ゴールでは[n0]が表れています。
  このまま証明を追える方法を探し続けることもできなくはありませんが、結局は基本的な戦略を変えるほうが得策です。
  [n]の構造についての帰納法ではなく、_[even]の証明の構造についての帰納法_を使うことにしましょう。
  この技法は、プログラミング言語の意味論では一般的に%\index{ルール帰納法}% _ルール帰納法_（rule induction）と呼ばれています。
  すでに見たように、Coqにおける命題の定義では、データ型と同じ帰納型の仕組みを使います。
  ルール帰納法と「ふつう」の帰納法の間にも、同じように根本的な統一関係があります。

  (* Recall that tactics like [induction] and [destruct] may be passed numbers to refer to unnamed lefthand sides of implications in the conclusion, where the argument [n] refers to the [n]th such hypothesis. *)
  
  [induction]や[destruct]のようなタクティクでは、[n]番めの仮定を指定したい場合には[n]を引数として指定するというように、結論の含意の左側にある無名の仮定を数字で指定できました。

Restart.

  induction 1.
(** <<
  m : nat
  ============================
   even m -> even (0 + m)
>>

(* %\noindent \coqdockw{subgoal} 2 \coqdockw{is}:%#<tt>subgoal 2 is</tt># *)

二つめのサブゴールはこうです。

<<
 even m -> even (S (S n) + m)
>>

(* The first case is easily discharged by [crush], based on the hint we added earlier to try the constructors of [even]. *)

最初のサブゴール[even m -> even (0 + m)]は、[crush]で簡単に証明できます。
これは、[even]の構成子を試すようにヒントを与えているからです。

*)

  crush.

  (**
  
  (* Now we focus on the second case: *)
  ここで二つめの場合分けを考えます。
  
  *)

  intro.
  (** <<
  m : nat
  n : nat
  H : even n
  IHeven : even m -> even (n + m)
  H0 : even m
  ============================
   even (S (S n) + m)
  >>

  (* We simplify and apply a constructor, as in our last proof attempt. *)
  
  先に証明を試みたときと同様、簡約して構成子を適用します。
  *)
  
  simpl; constructor.

(** <<
  ============================
   even (n + m)
   >>

  (* Now we have an exact match with our inductive hypothesis, and the remainder of the proof is trivial. *)
  
  これで帰納法の仮定と合致する形になりました。残りの証明は自明です。
  *)

  apply IHeven; assumption.

  (**
  (* In fact, [crush] can handle all of the details of the proof once we declare the induction strategy. *)
  
  いったん帰納法の戦略を宣言すれば、証明の細部はすべて[crush]で済ませられます。
  *)

Restart.

  induction 1; crush.
(* end thide *)
Qed.

(**
(* Induction on recursive predicates has similar pitfalls to those we encountered with inversion in the last section. *)

再帰的な命題についての帰納法にも、前節で逆転のときに遭遇したのと同様な落とし穴があります。
*)

Theorem even_contra : forall n, even (S (n + n)) -> False.
(* begin thide *)
  induction 1.
  (** <<
  n : nat
  ============================
   False
  >>

(* %\noindent \coqdockw{subgoal} 2 \coqdockw{is}:%#<tt>subgoal 2 is</tt># *)

二つめのサブゴールはこうなります。
<<
 False
>>

(* We are already sunk trying to prove the first subgoal, since the argument to [even] was replaced by a fresh variable internally.  This time, we find it easier to prove this theorem by way of a lemma.  Instead of trusting [induction] to replace expressions with fresh variables, we do it ourselves, explicitly adding the appropriate equalities as new assumptions. *)

[even]の引数が内部で新しい自由変数に置き換えられたので、一つめのサブゴールの証明はすでに撃沈しています。
この場合は、補題（Lemma）を用意することで、定理の証明が簡単になります。
適切な等式を新しい仮定として追加することで、[induction]による新しい自由変数への置き換えを代わりに自分たちでやることにします。
*)

Abort.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  induction 1; crush.

  (**
  (* At this point, it is useful to consider all cases of [n] and [n0] being zero or nonzero.  Only one of these cases has any trickiness to it. *)
  
  この時点で、[n]と[n0]に関する場合分けがすべてゼロか否ゼロであることを考慮しておきましょう。
  注意が必要なのは、それらのうち一つの場合だけです。
  *)

  destruct n; destruct n0; crush.

  (** <<
  n : nat
  H : even (S n)
  IHeven : forall n0 : nat, S n = S (n0 + n0) -> False
  n0 : nat
  H0 : S n = n0 + S n0
  ============================
   False
  >>

  (* At this point it is useful to use a theorem from the standard library, which we also proved with a different name in the last chapter.  We can search for a theorem that allows us to rewrite terms of the form [x + S y]. *)
  
  ここで標準ライブラリの定理を使います。なお、前章では同じ定理を別の名前で証明しています。
  [x + S y]という形式の項を書き換えられる定理を探してみましょう。
<<
  SearchRewrite (_ + S _).
    plus_n_Sm : forall n m : nat, S (n + m) = n + S m
>>
     *)

  rewrite <- plus_n_Sm in H0.

  (**
  (* The induction hypothesis lets us complete the proof, if we use a variant of [apply] that has a %\index{tactics!with}%[with] clause to give instantiations of quantified variables. *)
  
  [apply]には、限量化された変数についての指示を%\index{tactics!with}%[with]節で指定できます。
  これを使えば、帰納法の仮定により、証明は完了です。
  *)

  apply IHeven with n0; assumption.

  (**
  (* As usual, we can rewrite the proof to avoid referencing any locally generated names, which makes our proof script more readable and more robust to changes in the theorem statement.  We use the notation [<-] to request a hint that does right-to-left rewriting, just like we can with the [rewrite] tactic. *)

  いつものように、局所的に生成された名前の参照がなくなるように証明を書き換えることで、証明のスクリプトが読みやすく、かつ定理の文面の変更に対してより強固にします。
  ここでは、書き換えのヒントを与えるのに[<-]という記法を使っています。これにより、[rewrite]タクティクで[<-]を指定したときと同じように、右辺から左辺への書き換えが実施されます。
  *)

  Restart.

  Hint Rewrite <- plus_n_Sm.

  induction 1; crush;
    match goal with
      | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.
Qed.

(**
(* We write the proof in a way that avoids the use of local variable or hypothesis names, using the %\index{tactics!match}%[match] tactic form to do pattern-matching on the goal.  We use unification variables prefixed by question marks in the pattern, and we take advantage of the possibility to mention a unification variable twice in one pattern, to enforce equality between occurrences.  The hint to rewrite with [plus_n_Sm] in a particular direction saves us from having to figure out the right place to apply that theorem. *)

この証明では、%\index{tactics!match}%[match]タクティクの形式を使ってゴールに対するパターンマッチを実施することで、局所変数や仮定の名前を使わないように書かれています。
パターンではクエスチョンマークを前置した単一化変数を使っています。また、一つのパターンに単一化変数が二回出てくることを利用して、それらが等価性を主張しています。
[plus_n_Sm]による書き換えを左辺から右辺へ行うというヒントを与えているので、この定理を適用すべき適切な場面を見定める必要がありません。

(* The original theorem now follows trivially from our lemma, using a new tactic %\index{tactics!eauto}%[eauto], a fancier version of [auto] whose explanation we postpone to Chapter 13. *)

定理は、補題から自明に従います。
これには%\index{tactics!eauto}%[eauto]タクティクという、[auto]の便利な亜種を使います。
[eauto]の説明は第13章までお預けです。

*)

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.

(** 

(* We use a variant %\index{tactics!apply}%[eapply] of [apply] which has the same relationship to [apply] as [eauto] has to [auto].  An invocation of [apply] only succeeds if all arguments to the rule being used can be determined from the form of the goal, whereas [eapply] will introduce unification variables for undetermined arguments.  In this case, [eauto] is able to determine the right values for those unification variables, using (unsurprisingly) a variant of the classic algorithm for _unification_ %\cite{unification}%. *)

[auto]の代わりに[eauto]を使う必要があるように、[apply]の代わりに%\index{tactics!apply}%[eapply]という亜種を使っています。
[apply]は、利用されている規則の引数がすべてゴールの形式から決定可能な場合にのみ成功しますが、[eapply]は未決定の引数に対して単一化変数を導入してくれます。
導入された単一化変数の値は、この例の場合、_ユニフィケーション_ %\cite{unification}%のための古典的なアルゴリズムを使うことで[eauto]により適切に決定されます。

(* By considering an alternate attempt at proving the lemma, we can see another common pitfall of inductive proofs in Coq.  Imagine that we had tried to prove [even_contra'] with all of the [forall] quantifiers moved to the front of the lemma statement. *)

補題に対する別証明を考えることで、Coqにおける帰納的な証明に共通するまた別の落とし穴が見えてきます。
限量化子[forall]をすべて補題の言明の前に移動した[even_contra']という補題を証明しようとしたとしましょう。
*)

Lemma even_contra'' : forall n' n, even n' -> n' = S (n + n) -> False.
  induction 1; crush;
    match goal with
      | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.

  (**
   (* One subgoal remains: *)
   サブゴールが一つ残ります。
  <<
  n : nat
  H : even (S (n + n))
  IHeven : S (n + n) = S (S (S (n + n))) -> False
  ============================
   False
  >>

  (* We are out of luck here.  The inductive hypothesis is trivially true, since its assumption is false.  In the version of this proof that succeeded, [IHeven] had an explicit quantification over [n].  This is because the quantification of [n] _appeared after the thing we are inducting on_ in the theorem statement.  In general, quantified variables and hypotheses that appear before the induction object in the theorem statement stay fixed throughout the inductive proof.  Variables and hypotheses that are quantified after the induction object may be varied explicitly in uses of inductive hypotheses. *)

ここで手詰まりになります。
帰納法の仮定は、仮定が偽なので明らかに成り立ちます。
この証明は、[IHeven]において[n]が追加で限量化されている場合にはうまくいきます。
なぜなら、[n]の限量化は_帰納法の対象の後_に現れるからです。
一般に、定理の言明において帰納的な対象より前に限量化された変数と仮定が現れる場合、その言明は帰納法による証明の最中に変化していきません。
帰納的な対象の後で限量化されている変数や仮定であれば、帰納法の仮定を利用できる形で変化する可能性があります。
  *)


Abort.

(**
(* Why should Coq implement [induction] this way?  One answer is that it avoids burdening this basic tactic with additional heuristic smarts, but that is not the whole picture.  Imagine that [induction] analyzed dependencies among variables and reordered quantifiers to preserve as much freedom as possible in later uses of inductive hypotheses.  This could make the inductive hypotheses more complex, which could in turn cause particular automation machinery to fail when it would have succeeded before.  In general, we want to avoid quantifiers in our proofs whenever we can, and that goal is furthered by the refactoring that the [induction] tactic forces us to do. *)

Coqにおいて[induction]がこのように実装されているのはなぜでしょうか。
[induction]は基本的なタクティクであり、そこに余分なヒューリスティックを求めることによる負担を回避したいというのが一つの理由ですが、それだけではありません。
もし[induction]が変数間の依存関係を解析し、後段で帰納法の仮定をできるだけ自由に使えるように限量化子の順番を並べ替えてくれるとしたら、どうでしょうか。
その場合には、帰納法の仮定が複雑になり、結果として、本来なら成功するはずの自動化の仕組みが失敗するようになる可能性があります。
一般に、証明では限量化子をできるだけ避け、[induction]タクティクによって強制されるような仕方でゴールが書き換えられるほうが都合がいいのです。

*)

(* end thide *)




(* begin hide *)
(* In-class exercises *)

(* EX: Define a type [prop] of simple Boolean formulas made up only of truth, falsehood, binary conjunction, and binary disjunction.  Define an inductive predicate [holds] that captures when [prop]s are valid, and define a predicate [falseFree] that captures when a [prop] does not contain the "false" formula.  Prove that every false-free [prop] is valid. *)

(* begin thide *)
Inductive prop : Set :=
| Tru : prop
| Fals : prop
| And : prop -> prop -> prop
| Or : prop -> prop -> prop.

Inductive holds : prop -> Prop :=
| HTru : holds Tru
| HAnd : forall p1 p2, holds p1 -> holds p2 -> holds (And p1 p2)
| HOr1 : forall p1 p2, holds p1 -> holds (Or p1 p2)
| HOr2 : forall p1 p2, holds p2 -> holds (Or p1 p2).

Inductive falseFree : prop -> Prop :=
| FFTru : falseFree Tru
| FFAnd : forall p1 p2, falseFree p1 -> falseFree p2 -> falseFree (And p1 p2)
| FFNot : forall p1 p2, falseFree p1 -> falseFree p2 -> falseFree (Or p1 p2).

Hint Constructors holds.

Theorem falseFree_holds : forall p, falseFree p -> holds p.
  induction 1; crush.
Qed.
(* end thide *)


(* EX: Define an inductive type [prop'] that is the same as [prop] but omits the possibility for falsehood.  Define a proposition [holds'] for [prop'] that is analogous to [holds].  Define a function [propify] for translating [prop']s to [prop]s.  Prove that, for any [prop'] [p], if [propify p] is valid, then so is [p]. *)

(* begin thide *)
Inductive prop' : Set :=
| Tru' : prop'
| And' : prop' -> prop' -> prop'
| Or' : prop' -> prop' -> prop'.

Inductive holds' : prop' -> Prop :=
| HTru' : holds' Tru'
| HAnd' : forall p1 p2, holds' p1 -> holds' p2 -> holds' (And' p1 p2)
| HOr1' : forall p1 p2, holds' p1 -> holds' (Or' p1 p2)
| HOr2' : forall p1 p2, holds' p2 -> holds' (Or' p1 p2).

Fixpoint propify (p : prop') : prop :=
  match p with
    | Tru' => Tru
    | And' p1 p2 => And (propify p1) (propify p2)
    | Or' p1 p2 => Or (propify p1) (propify p2)
  end.

Hint Constructors holds'.

Lemma propify_holds' : forall p', holds p' -> forall p, p' = propify p -> holds' p.
  induction 1; crush; destruct p; crush.
Qed.

Theorem propify_holds : forall p, holds (propify p) -> holds' p.
  intros; eapply propify_holds'; eauto.
Qed.
(* end thide *)

(* end hide *)
