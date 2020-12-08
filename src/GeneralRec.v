(* Copyright (c) 2006, 2011-2012, 2015, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)
Require Import Arith List Omega.

Require Import Cpdt.CpdtTactics Cpdt.Coinductive.

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)


(**
(* %\chapter{General Recursion}% *)
%\chapter{一般的再帰}%

(**
(* Termination of all programs is a crucial property of Gallina.  Non-terminating programs introduce logical inconsistency, where any theorem can be proved with an infinite loop.  Coq uses a small set of conservative, syntactic criteria to check termination of all recursive definitions.  These criteria are insufficient to support the natural encodings of a variety of important programming idioms.  Further, since Coq makes it so convenient to encode mathematics computationally, with functional programs, we may find ourselves wanting to employ more complicated recursion in mathematical definitions. *)

Gallinaにとって、すべてのプログラムが停止するという性質はとても重要です。
停止しないプログラムは論理の不正後を引き起こし、任意の定理が無限ループによって証明できてしまいます。
Coqでは、すべての再帰的な定義が停止することを、シンタックスに対する少数の保守的な条件によって確かめます。
これらの条件は、プログラミングでよく使われる多様なイディオムをCoqでも自然に利用できるようにするには不十分です。
さらに、関数プログラミングを使って数学を計算的に扱うのに便利なCoqでは、より複雑な再帰を数学的な定義で使いたくなることもあるでしょう。

(* What exactly are the conservative criteria that we run up against?  For _recursive_ definitions, recursive calls are only allowed on _syntactic subterms_ of the original primary argument, a restriction known as%\index{primitive recursion}% _primitive recursion_.  In fact, Coq's handling of reflexive inductive types (those defined in terms of functions returning the same type) gives a bit more flexibility than in traditional primitive recursion, but the term is still applied commonly.  In Chapter 5, we saw how _co-recursive_ definitions are checked against a syntactic guardedness condition that guarantees productivity. *)

ここで懸念材料となっている保守的な条件とは、正確にはどんなものでしょうか。
_[再帰的]_な定義においては、もとの主引数の_[シンタックス上の部分項]_にのみ再帰呼び出しが許されます。
この制限は%\index{プリミティブな再帰}% _[プリミティブな再帰]_（primitive recursion）として知られているものです。
実を言うとCoqにおけるプリミティブな再帰は、相互再帰型（同じ型を返す複数の関数を使って定義された型）の扱いについて、伝統的なものに比べると多少柔軟になっています。
しかし、通例として、プリミティブな再帰という同じ用語が使われています。
第5章では、_[余再帰的]_な定義について、生成性を保証するためにシンタックスに対するガード条件が調べられることを見ました。

(* Many natural recursion patterns satisfy neither condition.  For instance, there is our simple running example in this chapter, merge sort.  We will study three different approaches to more flexible recursion, and the latter two of the approaches will even support definitions that may fail to terminate on certain inputs, without any up-front characterization of which inputs those may be. *)

自然な再帰には、どの条件も満たさないパターンが多くあります。
その一例は、本章で見るマージソートです。
本章では、より柔軟な再帰を実現する手法を三通り見ていきます。
そのうち後半の二つは、特定の入力に対して停止しない場合があるという定義さえ可能な方法です。
どのような入力であるかを事前に特徴づける必要もありません。

(* Before proceeding, it is important to note that the problem here is not as fundamental as it may appear.  The final example of Chapter 5 demonstrated what is called a%\index{deep embedding}% _deep embedding_ of the syntax and semantics of a programming language.  That is, we gave a mathematical definition of a language of programs and their meanings.  This language clearly admitted non-termination, and we could think of writing all our sophisticated recursive functions with such explicit syntax types.  However, in doing so, we forfeit our chance to take advantage of Coq's very good built-in support for reasoning about Gallina programs.  We would rather use a%\index{shallow embedding}% _shallow embedding_, where we model informal constructs by encoding them as normal Gallina programs.  Each of the three techniques of this chapter follows that style. *)

先に進む前に、こうした条件が必要であることが実はそれほど根源的なものではない、という点を注意しておきましょう。
第5章の最後に紹介した例は、プログラミング言語のシンタックスとセマンティクスを%\index{深い埋め込み}% _深く埋め込み_したものでした。
言い換えると、あるプログラムの言語に対して数学的な定義とその意味の両方を与える例を見ました。
そのように構成したプログラミング言語では、停止しないプログラムでも明らかに許容され、形式的な型を明示した精巧な再帰関数がなんでも書けるようになるでしょう。
しかし、それはまた、Coqに組み込まれた実に優れた機能であるGallinaのプログラムに関する推論を手放すことを意味します。
ここではむしろ、そのような深い埋め込みの代わりに、%\index{浅い埋め込み}%_浅い埋め込み_と呼ぶべき手法を使います。
具体的には、非形式的な構成要素を、通常のGallinaのプログラムとしてモデル化します。
本章で紹介する三つの技法は、いずれもこの浅い埋め込みによるものです。
*)

(**
(* * Well-Founded Recursion *)*

* 整礎な再帰
*)

(**
(* The essence of terminating recursion is that there are no infinite chains of nested recursive calls.  This intuition is commonly mapped to the mathematical idea of a%\index{well-founded relation}% _well-founded relation_, and the associated standard technique in Coq is%\index{well-founded recursion}% _well-founded recursion_.  The syntactic-subterm relation that Coq applies by default is well-founded, but many cases demand alternate well-founded relations.  To demonstrate, let us see where we get stuck on attempting a standard merge sort implementation. *)

再帰の停止にとって本質的なのは、再帰呼び出しの入れ子が無限に連鎖しないことです。
これは一般には数学における%\index{整礎関係}% _{整礎関係}_という概念に対応します。
それに対応する標準的なCoqの技法は%\index{整礎な再帰}% _{整礎な再帰}_です。
Coqにおいて、シンタックス上のサブ項に適用される関係は、デフォルトで整礎な関係です。
しかし、その整礎な関係に対して変更が求められる場合も多々あります。
標準的なマージソートの実装に挑戦しながら、どこで壁に直面するか見てみましょう。
*)

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  (**
  (* We have a set equipped with some "less-than-or-equal-to" test. *)
  
  上記の[A]は、「小なりイコール」をテストする仕組みを備えた集合のつもりです。
  *)

  (**
  (* A standard function inserts an element into a sorted list, preserving sortedness. *)
  
  下記は、ソート済みのリストに対してソートされた状態を維持したまま要素を追加する、標準的な関数です。
  *)

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
	if le x h
	  then x :: ls
	  else h :: insert x ls'
    end.

  (**
  (* We will also need a function to merge two sorted lists.  (We use a less efficient implementation than usual, because the more efficient implementation already forces us to think about well-founded recursion, while here we are only interested in setting up the example of merge sort.) *)
  
  2つのソート済みのリストをマージする関数も必要です。
  （下記の定義は、普通の実装よりも効率が悪いですが、効率を上げようと思うと、この時点で整礎な再帰についての考慮が必要になります。今はマージソートの例題に使うヘルパー関数を用意したいだけなので、効率は気にしないことにします。）
  *)

  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  (**
  (* The last helper function for classic merge sort is the one that follows, to split a list arbitrarily into two pieces of approximately equal length. *)
  
  最後に、ほぼ同じ長さを持つ2つの部分へとリストを任意に分割する下記のようなヘルパー関数を用意します。
  *)

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
	let (ls1, ls2) := split ls' in
	  (h1 :: ls1, h2 :: ls2)
    end.

  (**
  (* Now, let us try to write the final sorting function, using a natural number "[<=]" test [leb] from the standard library.*)
  
  それではマージソートを実行する関数を書いてみましょう。
  標準ライブラリには、自然数の「小なりイコール」をテストする[leb]という関数があるので、それを使います。
[[
  Fixpoint mergeSort (ls : list A) : list A :=
    if leb (length ls) 1
      then ls
      else let lss := split ls in
	merge (mergeSort (fst lss)) (mergeSort (snd lss)).
]]

<<
Recursive call to mergeSort has principal argument equal to
"fst (split ls)" instead of a subterm of "ls".
>>

(* The definition is rejected for not following the simple primitive recursion criterion.  In particular, it is not apparent that recursive calls to [mergeSort] are syntactic subterms of the original argument [ls]; indeed, they are not, yet we know this is a well-founded recursive definition. *)

上記の定義が受け入れられないのは、原始再帰における単純な基準に従っていないためです。
特に、[mergeSort]の再帰呼び出しが、元の引数[ls]のシンタックス上のサブ項に対するものになっているかどうかが明らかではありません。
実際、そうなっていないのですが、それでもこの定義は整礎な再帰的定義です。

(* To produce an acceptable definition, we need to choose a well-founded relation and prove that [mergeSort] respects it.  A good starting point is an examination of how well-foundedness is formalized in the Coq standard library. *)

受け入れられる定義を書くには、[mergeSort]が何らかの整礎関係を遵守していることを証明する必要があります。
手始めに、Coqの標準ライブラリにおいて整礎であることがどのように定式化されているかを調べてみましょう。
*)

  Print well_founded.
  (**  [[
well_founded = 
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
]]
*)

(* The bulk of the definitional work devolves to the%\index{accessibility relation}\index{Gallina terms!Acc}% _accessibility_ relation [Acc], whose definition we may also examine. *)

この定義の要点は、[Acc]という関係に集約されます。
これは%\index{accessibility relation}\index{Gallina terms!Acc}% _到達可能性関係_と呼ばれるものです。
[Acc]の定義を見てみましょう。
*)

(* begin hide *)
(* begin thide *)
Definition Acc_intro' := Acc_intro.
(* end thide *)
(* end hide *)

  Print Acc.
(**  [[
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
]]
*)

(* In prose, an element [x] is accessible for a relation [R] if every element "less than" [x] according to [R] is also accessible.  Since [Acc] is defined inductively, we know that any accessibility proof involves a finite chain of invocations, in a certain sense that we can make formal.  Building on Chapter 5's examples, let us define a co-inductive relation that is closer to the usual informal notion of "absence of infinite decreasing chains." *)

この定義を文章にすれば、「[x]が関係[R]に対して到達可能性がある」というのは、[x]との間で関係[R]にあるすべての要素（つまり[x]より小さなすべての要素）もまた[R]に対して到達可能性がある場合である、となります。
[Acc]の定義が帰納的なので、到達可能性関係の証明には「有限回の呼び出しの連鎖」が関与することが（そのことを形式化できるという意味で）わかります。
第5章の例を参考に、「無限に下降する連鎖がない」という通常の非形式的な表現に近い余帰納関係を定義してみましょう。
*)

  CoInductive infiniteDecreasingChain A (R : A -> A -> Prop) : stream A -> Prop :=
  | ChainCons : forall x y s, infiniteDecreasingChain R (Cons y s)
    -> R y x
    -> infiniteDecreasingChain R (Cons x (Cons y s)).

(**
(* We can now prove that any accessible element cannot be the beginning of any infinite decreasing chain. *)

上記を使うと、「到達可能な要素から始まる連鎖が無限に下降することはない」ことが証明できます。
*)

(* begin thide *)
  Lemma noBadChains' : forall A (R : A -> A -> Prop) x, Acc R x
    -> forall s, ~infiniteDecreasingChain R (Cons x s).
    induction 1; crush;
      match goal with
        | [ H : infiniteDecreasingChain _ _ |- _ ] => inversion H; eauto
      end.
  Qed.

(**
(* From here, the absence of infinite decreasing chains in well-founded sets is immediate. *)

ここまでくれば、整礎な集合には無限に下降する連鎖がないことがすぐに導けます。
*)

  Theorem noBadChains : forall A (R : A -> A -> Prop), well_founded R
    -> forall s, ~infiniteDecreasingChain R s.
    destruct s; apply noBadChains'; auto.
  Qed.
(* end thide *)

(**
(* Absence of infinite decreasing chains implies absence of infinitely nested recursive calls, for any recursive definition that respects the well-founded relation.  The [Fix] combinator from the standard library formalizes that intuition: *)

無限に下降する連鎖がないことは、「整礎関係を遵守する再帰的な定義であれば、再帰呼び出しが無限に入れ子になることはない」ことを示唆します。
この直観を形式化するには、標準ライブラリの[Fix]結合子が使えます。
*)

  Check Fix.
(** [[
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall x : A, P x
]]

(* A call to %\index{Gallina terms!Fix}%[Fix] must present a relation [R] and a proof of its well-foundedness.  The next argument, [P], is the possibly dependent range type of the function we build; the domain [A] of [R] is the function's domain.  The following argument has this type:*)

%\index{Gallina terms!Fix}%[Fix]を呼び出すときには、整礎関係の証明つきで、関係[R]を提示します。
[P]が表しているのは「組み立てる関数の値域の型（依存型の場合もある）」です（[R]の定義域である[A]が、その関数の定義域になります）。
それに続くのは、組み立てる関数の本体を表す次の型です。

[[
       forall x : A, (forall y : A, R y x -> P y) -> P x
]]

(* This is an encoding of the function body.  The input [x] stands for the function argument, and the next input stands for the function we are defining.  Recursive calls are encoded as calls to the second argument, whose type tells us it expects a value [y] and a proof that [y] is "less than" [x], according to [R].  In this way, we enforce the well-foundedness restriction on recursive calls. *)

[x]は組み立てる関数の引数に相当します。定義している関数に相当するのが[(forall y : A, R y x -> P y) -> P x]です。
この[Fix]の二つめの引数が、再帰呼び出しを表しています。その型からわかるように、この二つめの引数は、[x]との間で関係[R]にある（つまり[x]より「小さい」）ことの証明付きで値[y]を取ります。

(* The rest of [Fix]'s type tells us that it returns a function of exactly the type we expect, so we are now ready to use it to implement [mergeSort].  Careful readers may have noticed that [Fix] has a dependent type of the sort we met in the previous chapter. *)

[Fix]の型の最後の部分を見ると、[Fix]が期待どおりの型を持つ関数を返すことがわかります。
そこで、この[Fix]を使って[mergeSort]を書くことにします。
[Fix]が前章で見たような依存型を持つことに気が付いた読者もいることでしょう。

(* Before writing [mergeSort], we need to settle on a well-founded relation.  The right one for this example is based on lengths of lists. *)

[mergeSort]を書く前に、整礎な関係を定めておく必要があります。
今の例ではリストの長さに対する関係として定義しましょう。
*)

  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  (**
  (* We must prove that the relation is truly well-founded.  To save some space in the rest of this chapter, we skip right to nice, automated proof scripts, though we postpone introducing the principles behind such scripts to Part III of the book.  Curious readers may still replace semicolons with periods and newlines to step through these scripts interactively. *)
  
  この関係が整礎であることを証明しなければなりません。
  本章があまり長くならないように、ここはうまく自動証明スクリプトで片づけることにします。ただし、このスクリプトの背景にある原理の説明は第III部まで持ち越します。
  興味がある読者は、セミコロンをピリオドと改行に置き換えて、スクリプトの各ステップを対話的に実行してみてもいいでしょう。
  *)

  Hint Constructors Acc.

  Lemma lengthOrder_wf' : forall len, forall ls, length ls <= len -> Acc lengthOrder ls.
    unfold lengthOrder; induction len; crush.
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
    red; intro; eapply lengthOrder_wf'; eauto.
  Defined.

  (**
  (* Notice that we end these proofs with %\index{Vernacular commands!Defined}%[Defined], not [Qed].  Recall that [Defined] marks the theorems as %\emph{%#<i>#transparent#</i>#%}%, so that the details of their proofs may be used during program execution.  Why could such details possibly matter for computation?  It turns out that [Fix] satisfies the primitive recursion restriction by declaring itself as _recursive in the structure of [Acc] proofs_.  This is possible because [Acc] proofs follow a predictable inductive structure.  We must do work, as in the last theorem's proof, to establish that all elements of a type belong to [Acc], but the automatic unwinding of those proofs during recursion is straightforward.  If we ended the proof with [Qed], the proof details would be hidden from computation, in which case the unwinding process would get stuck.  *)

  上記では、[Qed]ではなく%\index{Vernacular commands!Defined}%[Defined]を使って証明を終えています。
  [Defined]を使うと、証明が%\emph{%#<i>#透明#</i>#%}%になり、プログラムの実行中に証明の細部が使われるようになるのでした。
  この証明の細部を計算で利用できることには、何か意味があるのでしょうか？
  実は[Fix]は、自身が_{[Acc]の証明の構造に関して再帰的である}_と宣言することで、プリミティブな再帰の制限を満たすようになります。
  これが可能なのは、[Acc]の証明が、帰納法の構造に従った予測可能なものであることによります。
  最後の定理の証明では、型のすべての要素が[Acc]に属することを確立するという手間があるのですが、これは再帰の最中に証明の自動的な巻き上げが可能であれば簡単になります。
  もし[Qed]で証明を終えてしまうと、証明の細部が計算から隠されるので、この巻き上げが止まってしまうのです。

  (* To justify our two recursive [mergeSort] calls, we will also need to prove that [split] respects the [lengthOrder] relation.  These proofs, too, must be kept transparent, to avoid stuckness of [Fix] evaluation.  We use the syntax [@foo] to reference identifier [foo] with its implicit argument behavior turned off.  (The proof details below use Ltac features not introduced yet, and they are safe to skip for now.) *)
  
  [mergeSort]の二つの再帰呼び出しを正当化するには、[split]についても関係[lengthOrder]を遵守することの証明が必要です。
  その証明も[Fix]の実行が止まらないように透明にしておきます。
  なお、[@foo]というシンタックスは、暗黙の引数の挙動を無効にした状態で識別子[foo]を参照するものです。
  （下記の証明では、まだ説明していないLtacの機能を使っています。いまは読み飛ばして問題ありません。）
  *)

  Lemma split_wf : forall len ls, 2 <= length ls <= len
    -> let (ls1, ls2) := split ls in
      lengthOrder ls1 ls /\ lengthOrder ls2 ls.
    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[split ?L] ] =>
                    specialize (IH L); destruct (split L); destruct IH
                end; crush).
  Defined.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
    destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls, 2 <= length ls
    -> lengthOrder (fst (split ls)) ls.
    split_wf.
  Defined.

  Lemma split_wf2 : forall ls, 2 <= length ls
    -> lengthOrder (snd (split ls)) ls.
    split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.

  (**
  (* To write the function definition itself, we use the %\index{tactics!refine}%[refine] tactic as a convenient way to write a program that needs to manipulate proofs, without writing out those proofs manually.  We also use a replacement [le_lt_dec] for [leb] that has a more interesting dependent type.  (Note that we would not be able to complete the definition without this change, since [refine] will generate subgoals for the [if] branches based only on the _type_ of the test expression, not its _value_.) *)
  
  関数の定義そのものは、%\index{tactics!refine}%[refine]タクティクを使って書きます。
  [refine]は、証明を手作業で書き下すことなく、証明を操作する必要があるプログラムを書くときに便利な手法です。
  また、[leb]の代わりに、依存型を持つ[le_lt_dec]を使っています。
  （[refine]では、[if]節の分岐に対してサブゴールを生成するときに条件式の_値_ではなく_型_のみを利用するので、[le_lt_dec]を使わずに証明を完了することはできないでしょう。）
  *)

  Definition mergeSort : list A -> list A.
(* begin thide *)
    refine (Fix lengthOrder_wf (fun _ => list A)
      (fun (ls : list A)
        (mergeSort : forall ls' : list A, lengthOrder ls' ls -> list A) =>
        if le_lt_dec 2 (length ls)
	  then let lss := split ls in
            merge (mergeSort (fst lss) _) (mergeSort (snd lss) _)
	  else ls)); subst lss; eauto.
  Defined.
(* end thide *)
End mergeSort.

(**
(* The important thing is that it is now easy to evaluate calls to [mergeSort]. *)

これで[mergeSort]の呼び出しを簡単に実行できるようになりました。
*)

Eval compute in mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).
(** [= 1 :: 2 :: 8 :: 19 :: 36 :: nil] *)

(**
(* %\smallskip{}%Since the subject of this chapter is merely how to define functions with unusual recursion structure, we will not prove any further correctness theorems about [mergeSort]. Instead, we stop at proving that [mergeSort] has the expected computational behavior, for all inputs, not merely the one we just tested. *)

本章の目標は通常とは違う再帰の構造をもった関数を定義する方法を説明することなので、[mergeSort]の正しさに関する他の定理を証明することはしません。
その代わり、ここでちょっと立ち止まって、[mergeSort]が上記で試した例だけでなくあらゆる入力に対して期待通りの計算的な挙動になることを証明してみましょう。
*)

(* begin thide *)
Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
  mergeSort le ls = if le_lt_dec 2 (length ls)
    then let lss := split ls in
      merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
    else ls.
  intros; apply (Fix_eq (@lengthOrder_wf A) (fun _ => list A)); intros.

  (**
  (* The library theorem [Fix_eq] imposes one more strange subgoal upon us.  We must prove that the function body is unable to distinguish between "self" arguments that map equal inputs to equal outputs.  One might think this should be true of any Gallina code, but in fact this general%\index{extensionality}% _function extensionality_ property is neither provable nor disprovable within Coq.  The type of [Fix_eq] makes clear what we must show manually: *)
  
  ライブラリにある[Fix_eq]という定理は、さらに一つ、奇妙なサブゴールを提示します。
  関数の本体が、等しい入力に対して等しい出力を対応させるような引数どうしの間で、互いに区別がないことを証明する必要があるのです。
  これは%\index{外延性}% _関数の外延性_と呼ばれる性質です。
  関数の外延性は、Gallinaのコードであれば真であるように思えるかもしれませんが、実際にはCoqの中で証明可能でも証明不能でもありません。
  [Fix_eq]の型を見ると、証明すべきことが何であるかがはっきりとわかります。
  *)

  Check Fix_eq.
(** %\vspace{-.15in}%[[
Fix_eq
     : forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R)
         (P : A -> Type)
         (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
       (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g) ->
       forall x : A,
       Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y)
]]

  (* Most such obligations are dischargeable with straightforward proof automation, and this example is no exception. *)
  
  こうした証明の責務は、その多くが単純な証明の自動化によって片づきます。今回も例外ではありません。
  *)

  match goal with
    | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
  end; simpl; f_equal; auto.
Qed.
(* end thide *)

(**
(* As a final test of our definition's suitability, we can extract to OCaml. *)

適切に定義できているかどうか、最後にOCamlのコードを抽出して確かめてみましょう。
*)

Extraction mergeSort.

(** <<
let rec mergeSort le x =
  match le_lt_dec (S (S O)) (length x) with
  | Left ->
    let lss = split x in
    merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
  | Right -> x
>>

(*  We see almost precisely the same definition we would have written manually in OCaml!  It might be a good exercise for the reader to use the commands we saw in the previous chapter to clean up some remaining differences from idiomatic OCaml.

OCamlで手で書くであろうコードとほぼ同じ定義が得られました。
前章で説明したコマンドを使って、OCamlのイディオムとの差をもう少し詰めてみると、よい練習になるでしょう。
*)

(*  One more piece of the full picture is missing.  To go on and prove correctness of [mergeSort], we would need more than a way of unfolding its definition.  We also need an appropriate induction principle matched to the well-founded relation.  Such a principle is available in the standard library, though we will say no more about its details here. *)

もう一つ不足していることがあります。
[mergeSort]の正しさを証明するには、その定義を展開するだけでは不十分であり、整礎な関係に適合する適切な帰納法の原理も必要です。
ここでは詳細を省きますが、標準ライブラリにはそのような原理があります。
*)

Check well_founded_induction.
(** %\vspace{-.15in}%[[
well_founded_induction
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Set,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall a : A, P a
]]

(*  Some more recent Coq features provide more convenient syntax for defining recursive functions.  Interested readers can consult the Coq manual about the commands %\index{Function}%[Function] and %\index{Program Fixpoint}%[Program Fixpoint]. *)

比較的新しいCoqの機能には、再帰的な関数を定義するさらに便利なシンタックスもあります。
興味がある読者はCoqのマニュアルで%\index{Function}%[Function]および%\index{Program Fixpoint}%[Program Fixpoint]というコマンドを調べてみてください。
*)


(**
(* * A Non-Termination Monad Inspired by Domain Theory *)

* 領域理論と非停止性モナド
*)

(**
(* The key insights of %\index{domain theory}%domain theory%~\cite{WinskelDomains}% inspire the next approach to modeling non-termination.  Domain theory is based on _information orders_ that relate values representing computation results, according to how much information these values convey.  For instance, a simple domain might include values "the program does not terminate" and "the program terminates with the answer 5."  The former is considered to be an _approximation_ of the latter, while the latter is _not_ an approximation of "the program terminates with the answer 6."  The details of domain theory will not be important in what follows; we merely borrow the notion of an approximation ordering on computation results.*)

停止しないという概念のモデル化には、%\index{領域理論}%領域理論%~\cite{WinskelDomains}%の考え方も使えます。
領域理論は_情報の順番_に基づく理論です。計算の結果には「値がどれだけの情報を持っているか」に応じて順番をつけられます。
例として単純な領域を考えてみましょう。この領域には「プログラムが停止しない」とか「プログラムが5つの答えを出して停止する」といった値が含まれます。
領域理論では、一つの値は二つめの値の_近似_だとみなせます。一方、二つめの値は、「プログラムが6つの答えを出して停止する」の近似ではありません。
以降の説明では、領域理論の詳細を知っている必要はありません。「計算の結果に対する近似的な順序付け」の記法のみを領域理論から借りてきます。

(* Consider this definition of a type of computations. *)

以下のような計算の型の定義を考えてみましょう。
*)

Section computation.
  Variable A : Type.
  (**
  (* The type [A] describes the result a computation will yield, if it terminates.*)
  
  [A]という型は、計算が停止した場合に導出する結果を表しています。

  (*  We give a rich dependent type to computations themselves: *)
  
  計算そのものの型は、豊かな依存型とします。
  *)

  Definition computation :=
    {f : nat -> option A
      | forall (n : nat) (v : A),
	f n = Some v
	-> forall (n' : nat), n' >= n
	  -> f n' = Some v}.

  (**
  (* A computation is fundamentally a function [f] from an _approximation level_ [n] to an optional result.  Intuitively, higher [n] values enable termination in more cases than lower values.  A call to [f] may return [None] to indicate that [n] was not high enough to run the computation to completion; higher [n] values may yield [Some].  Further, the proof obligation within the subset type asserts that [f] is _monotone_ in an appropriate sense: when some [n] is sufficient to produce termination, so are all higher [n] values, and they all yield the same program result [v]. *)
  
  上記では、_{近似を表すレベル}_[n]から、省略可能な結果への関数[f]として、計算を定義しています。
  直観的には、[n]の値が大きいほど停止するプログラムは多くなります。
  [f]は、レベル[n]が計算の実行を完了できるほど十分に高くない場合には[None]を返すことがあります。
  一方、[n]の値が十分に大きければ[Some]が得られます。
  さらに、部分集合型に含まれるproof obligationでは、[f]が_一様である_ことが宣言されています。
  これは、「あるレベル[n]で停止する計算は[n]より大きなすべてのレベルでも停止し、それらのレベルで得られるプログラムの値[v]はすべて同一である」という意味です。
  
  (* It is easy to define a relation characterizing when a computation runs to a particular result at a particular approximation level. *)
  
  「特定の近似レベルで計算を実行すると特定の結果になる」場合については、簡単に関係を定義できます。
  *)

  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.

  (**
  (* On top of [runTo], we also define [run], which is the most abstract notion of when a computation runs to a value. *)
  
  [runTo]を使って[run]も定義します。この[run]が、計算を実行して値が得られる場合を抽象化した最終形です。
  *)

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
End computation.

(**
(* The book source code contains at this point some tactics, lemma proofs, and hint commands, to be used in proving facts about computations.  Since their details are orthogonal to the message of this chapter, I have omitted them in the rendered version. *)

実際のソースコードでは、計算についての事実を証明するために、この時点でいくつかのタクティク、補題の証明、ヒントのコマンドを使っています。
それらの詳細は本章で伝えるべき内容とは関係がないので、ここでは割愛してあります。
*)
(* begin hide *)

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.
(** remove printing exists *)
(* end hide *)

(**
(* Now, as a simple first example of a computation, we can define [Bottom], which corresponds to an infinite loop.  For any approximation level, it fails to terminate (returns [None]).  Note the use of [abstract] to create a new opaque lemma for the proof found by the #<tt>#%\coqdocvar{%run%}%#</tt># tactic.  In contrast to the previous section, opaque proofs are fine here, since the proof components of computations do not influence evaluation behavior.  It is generally preferable to make proofs opaque when possible, as this enforces a kind of modularity in the code to follow, preventing it from depending on any details of the proof. *)

単純な計算の例として、まずは[Bottom]を定義してみましょう。
[Bottom]は無限ループに対応し、どのような近似レベルでも停止に失敗します（つまり[None]を返します）。
#<tt>#%\coqdocvar{%run%}%#</tt>#タクティクによって見つかった証明のための補題を新しく作るのに、証明が透明ではない[abstract]を使っていることに注目してください。
前節と違って、この証明が透明である必要がないのは、計算の証明では、証明の要素が評価の挙動に影響しないからです。
一般に、証明はできるだけ透明でない状態にしておくほうがよいでしょう。
それによりコードに対して一種のモジュラリティが強制され、証明の詳細への依存が避けられます。
*)

Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v, ~run Bottom v.
    run.
  Qed.
End Bottom.

(**
(* A slightly more complicated example is [Return], which gives the same terminating answer at every approximation level. *)

次の例は、停止する同一の答えをすべての近似レベルで生成する[Return]です。こちらは少し複雑です。
*)

Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    intros; exists (fun _ : nat => Some v); abstract run.
  Defined.

  Theorem run_Return : run Return v.
    run.
  Qed.
End Return.

(**
(* The name [Return] was meant to be suggestive of the standard operations of %\index{monad}%monads%~\cite{Monads}%.  The other standard operation is [Bind], which lets us run one computation and, if it terminates, pass its result off to another computation.  We implement bind using the notation [let (x, y) := e1 in e2], for pulling apart the value [e1] which may be thought of as a pair.  The second component of a [computation] is a proof, which we do not need to mention directly in the definition of [Bind]. *)

[Return]という名称は、%\index{モナド}%モナド%~\cite{Monads}%の標準的な操作にちなみます。
モナドのもう一つの標準的な操作は[Bind]です。[Bind]は計算を一つ実行し、停止する場合にはその結果を別の計算に渡します。
実装で使っている[let (x, y) := e1 in e2]という記法は、ペアである値[e1]を分離するものです。
[computation]の二つめの要素は証明であり、こちらは[Bind]の定義で直接記述する必要がありません。
*)

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  Definition Bind : computation B.
    exists (fun n =>
      let (f1, _) := m1 in
      match f1 n with
	| None => None
	| Some v =>
	  let (f2, _) := m2 v in
	    f2 n
      end); abstract run.
  Defined.

  Theorem run_Bind : forall (v1 : A) (v2 : B),
    run m1 v1
    -> run (m2 v1) v2
    -> run Bind v2.
    run; match goal with
           | [ x : nat, y : nat |- _ ] => exists (max x y)
         end; run.
  Qed.
End Bind.

(**
(* A simple notation lets us write [Bind] calls the way they appear in Haskell. *)

単純な記法のおかげで、Haskellのような書き方で[Bind]を呼び出せます。
*)

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

(**
(* We can verify that we have indeed defined a monad, by proving the standard monad laws.  Part of the exercise is choosing an appropriate notion of equality between computations.  We use "equality at all approximation levels." *)

標準的なモナド則を証明することで、ここで定義したものが実際にモナドであることを検証できます。
ポイントは、計算と計算の間の等価性をどう設定するかです。
ここでは、「すべての近似レベルで等しい」という指標を使います。
*)

Definition meq A (m1 m2 : computation A) := forall n, proj1_sig m1 n = proj1_sig m2 n.

Theorem left_identity : forall A B (a : A) (f : A -> computation B),
  meq (Bind (Return a) f) (f a).
  run.
Qed.

Theorem right_identity : forall A (m : computation A),
  meq (Bind m (@Return _)) m.
  run.
Qed.

Theorem associativity : forall A B C (m : computation A)
  (f : A -> computation B) (g : B -> computation C),
  meq (Bind (Bind m f) g) (Bind m (fun x => Bind (f x) g)).
  run.
Qed.

(**
(* Now we come to the piece most directly inspired by domain theory.  We want to support general recursive function definitions, but domain theory tells us that not all definitions are reasonable; some fail to be _continuous_ and thus represent unrealizable computations.  To formalize an analogous notion of continuity for our non-termination monad, we write down the approximation relation on computation results that we have had in mind all along. *)

ここで領域理論をもっとも直接的に使います。
領域理論によると、すべての定義が推論可能なわけではなく、計算の_{継続}_に失敗する、つまり停止しない計算があります。
こうした計算に対しても一般再帰関数が定義できるようにしたいところです。
停止しないモナドに対する継続に類似した概念を形式化するため、これまで扱ってきた「計算の結果がどれだけ近似しているか」という関係を書き下してみます。
*)

Section lattice.
  Variable A : Type.

  Definition leq (x y : option A) :=
    forall v, x = Some v -> y = Some v.
End lattice.

(**
(* We now have the tools we need to define a new [Fix] combinator that, unlike the one we saw in the prior section, does not require a termination proof, and in fact admits recursive definition of functions that fail to terminate on some or all inputs. *)

これで新しい[Fix]結合子を定義する道具が揃いました。
この新しい[Fix]は、前節のものとは違い、停止することの証明を要求しません。
また、入力の一部もしくはすべてについて停止に失敗する関数の、再帰的な定義を受け入れます。
*)

Section Fix.

  (**
  (* First, we have the function domain and range types. *)
  
  まず、関数の定義域と値域の型を用意します。
  *)

  Variables A B : Type.

  (**
  (* Next comes the function body, which is written as though it can be parameterized over itself, for recursive calls. *)
  
  次は、関数の本体です。再帰的な呼び出しのため、自分自身をパラメータとして取ることが可能であるかのような書き方をします。
  *)

  Variable f : (A -> computation B) -> (A -> computation B).

  (**
  (* Finally, we impose an obligation to prove that the body [f] is continuous.  That is, when [f] terminates according to one recursive version of itself, it also terminates with the same result at the same approximation level when passed a recursive version that refines the original, according to [leq]. *)
  
  最後に、「本体[f]が継続する」ことについてproof obligationを課します。
  つまり、ある再帰的な定義で[f]が停止する場合には、別の再帰で改良したバージョンでも、[leq]による比較で近似レベルが同じなら、同じ結果を伴って停止することを証明します。
  *)

  Hypothesis f_continuous : forall n v v1 x,
    runTo (f v1 x) n v
    -> forall (v2 : A -> computation B),
      (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n))
      -> runTo (f v2 x) n v.

  (**
  (* The computational part of the [Fix] combinator is easy to define.  At approximation level 0, we diverge; at higher levels, we run the body with a functional argument drawn from the next lower level. *)
  
  [Fix]結合子で計算を扱う部分は簡単に定義できます。
  近似レベルが0の場合は発散、それより高いレベルでは、一つ下のレベルから取り出した関数の引数で、関数の本体を実行します。
  *)

  Fixpoint Fix' (n : nat) (x : A) : computation B :=
    match n with
      | O => Bottom _
      | S n' => f (Fix' n') x
    end.

  (**
  (* Now it is straightforward to package [Fix'] as a computation combinator [Fix]. *)
  
  この[Fix']を、そのまま計算の演算子[Fix]としてパッケージ化します。
  *)

  Hint Extern 1 (_ >= _) => omega.
  Hint Unfold leq.

  Lemma Fix'_ok : forall steps n x v, proj1_sig (Fix' n x) steps = Some v
    -> forall n', n' >= n
      -> proj1_sig (Fix' n' x) steps = Some v.
    unfold runTo in *; induction n; crush;
      match goal with
        | [ H : _ >= _ |- _ ] => inversion H; crush; eauto
      end.
  Qed.

  Hint Resolve Fix'_ok.

  Hint Extern 1 (proj1_sig _ _ = _) => simpl;
    match goal with
      | [ |- proj1_sig ?E _ = _ ] => eapply (proj2_sig E)
    end.

  Definition Fix : A -> computation B.
    intro x; exists (fun n => proj1_sig (Fix' n x) n); abstract run.
  Defined.

  (**
  (* Finally, we can prove that [Fix] obeys the expected computation rule. *)
  
  最後に、[Fix]が計算の規則に期待どおりに従うことを証明できます。
  *)

  Theorem run_Fix : forall x v,
    run (f Fix x) v
    -> run (Fix x) v.
    run; match goal with
           | [ n : nat |- _ ] => exists (S n); eauto
         end.
  Qed.
End Fix.

(* begin hide *)
Lemma leq_Some : forall A (x y : A), leq (Some x) (Some y)
  -> x = y.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Lemma leq_None : forall A (x y : A), leq (Some x) None
  -> False.
  intros ? ? ? H; generalize (H _ (eq_refl _)); crush.
Qed.

Ltac mergeSort' := run;
  repeat (match goal with
            | [ |- context[match ?E with O => _ | S _ => _ end] ] => destruct E
          end; run);
  repeat match goal with
           | [ H : forall x, leq (proj1_sig (?f x) _) (proj1_sig (?g x) _) |- _ ] =>
             match goal with
               | [ H1 : f ?arg = _, H2 : g ?arg = _ |- _ ] =>
                 generalize (H arg); rewrite H1; rewrite H2; clear H1 H2; simpl; intro
             end
         end; run; repeat match goal with
                            | [ H : _ |- _ ] => (apply leq_None in H; tauto) || (apply leq_Some in H; subst)
                          end; auto.
(* end hide *)

(**
(* After all that work, it is now fairly painless to define a version of [mergeSort] that requires no proof of termination.  We appeal to a program-specific tactic whose definition is hidden here but present in the book source. *)

ここまで準備すれば、停止性の証明が要求されないバージョンの[mergeSort]を定義するのも難しくありません。
プログラムに特化したタクティクに任せます（ここではタクティクの定義は割愛します）。
*)

Definition mergeSort' : forall A, (A -> A -> bool) -> list A -> computation (list A).
  refine (fun A le => Fix
    (fun (mergeSort : list A -> computation (list A))
      (ls : list A) =>
      if le_lt_dec 2 (length ls)
	then let lss := split ls in
          ls1 <- mergeSort (fst lss);
          ls2 <- mergeSort (snd lss);
          Return (merge le ls1 ls2)
	else Return ls) _); abstract mergeSort'.
Defined.

(**
(* Furthermore, "running" [mergeSort'] on concrete inputs is as easy as choosing a sufficiently high approximation level and letting Coq's computation rules do the rest.  Contrast this with the proof work that goes into deriving an evaluation fact for a deeply embedded language, with one explicit proof rule application per execution step. *)

具体的な入力例に対して[mergeSort']を「実行」するには、十分な高さの近似レベルを選び、残りの仕事はCoqの計算規則に任せるだけです。
実行ステップごとに一つの明示的な証明規則を適用して、深く埋め込まれた言語の評価に関する事実を導出する証明作業と比較すると、かなり簡単です。
*)

Lemma test_mergeSort' : run (mergeSort' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  exists 4; reflexivity.
Qed.

(**
(* There is another benefit of our new [Fix] compared with the one we used in the previous section: we can now write recursive functions that sometimes fail to terminate, without losing easy reasoning principles for the terminating cases.  Consider this simple example, which appeals to another tactic whose definition we elide here. *)

新しい[Fix]には、前節のものに比べ、ほかにも利点があります。
それは、停止する場合についての簡単な再帰の原理を損なうことなく、停止に失敗する場合があるような再帰的な関数が書けるようになったことです。
以下の単純な例を考えてみてください（タクティクの定義は割愛します）。
*)

(* begin hide *)
Ltac looper := unfold leq in *; run;
  repeat match goal with
           | [ x : unit |- _ ] => destruct x
           | [ x : bool |- _ ] => destruct x
         end; auto.
(* end hide *)

Definition looper : bool -> computation unit.
  refine (Fix (fun looper (b : bool) =>
    if b then Return tt else looper b) _); abstract looper.
Defined.

Lemma test_looper : run (looper true) tt.
  exists 1; reflexivity.
Qed.

(**
(* As before, proving outputs for specific inputs is as easy as demonstrating a high enough approximation level.*)

前と同様、特定の入力に対する出力に関する証明は、十分に高い近似レベルで実行を試してみるのと同じくらい簡単です。

(* There are other theorems that are important to prove about combinators like [Return], [Bind], and [Fix].  In general, for a computation [c], we sometimes have a hypothesis proving [run c v] for some [v], and we want to perform inversion to deduce what [v] must be.  Each combinator should ideally have a theorem of that kind, for [c] built directly from that combinator.  We have omitted such theorems here, but they are not hard to prove.  In general, the domain theory-inspired approach avoids the type-theoretic "gotchas" that tend to show up in approaches that try to mix normal Coq computation with explicit syntax types.  The next section of this chapter demonstrates two alternate approaches of that sort.  In the final section of the chapter, we review the pros and cons of the different choices, coming to the conclusion that none of them is obviously better than any one of the others for all situations. *)

[Return]、[Blind]、[Fix]のような結合子に関する証明では、ほかにも重要な定理があります。
結合子[c]に対して実行したい作業は、一般には逆転です。
つまり、ある[v]について[run c v]を証明する仮説があり、そのうえで[v]が何でなければならないかを導出したいことが多くあります。
理想的には、どの結合子にも、そこから[c]が直接組み立てられるような定理があるはずです。
本節では割愛しましたが、そのような定理の証明は難しくありません。
一般に、領域理論を応用したアプローチを採用すれば、通常のCoqの計算と明示的な構文の型とを一緒に扱うアプローチでは直面するような型理論にまつわる「面倒」を避けられます。
次節では、同様のアプローチをさらに二つ紹介します。
そして最後の節では、各アプローチの利点と欠点を振り返り、どのような状況でも明らかに他より優れていると言えるアプローチがないという結論を導きます。
*)


(**
(* * Co-Inductive Non-Termination Monads *)

* 余帰納的な非停止性モナド
*)

(**
(* There are two key downsides to both of the previous approaches: both require unusual syntax based on explicit calls to fixpoint combinators, and both generate immediate proof obligations about the bodies of recursive definitions.  In Chapter 5, we have already seen how co-inductive types support recursive definitions that exhibit certain well-behaved varieties of non-termination.  It turns out that we can leverage that co-induction support for encoding of general recursive definitions, by adding layers of co-inductive syntax.  In effect, we mix elements of shallow and deep embeddings.*)

これまでのアプローチには、いずれも二つの主な欠点があります。
どちらのアプローチでも[Fixpoint]を使った結合子を明示的に呼び出すような一般的でない構文が必要であることと、すぐに再帰的な定義の本体に関するproof obligationが生成されることです。
第5章では、停止しないことが正しい振る舞いであるような再帰的定義において余帰納型が役に立つことを見ました。
余帰納法は、一般再帰による定義を表現するうえでも、余帰納的な構文の層を追加するという形で活用できます。
具体的には、浅い埋め込みの要素と深い埋め込みの要素を混在させます。

(* Our first example of this kind, proposed by Capretta%~\cite{Capretta}%, defines a silly-looking type of thunks; that is, computations that may be forced to yield results, if they terminate. *)

最初の例は、Capretta%~\cite{Capretta}%によって提唱されたものです。
このアプローチでは、奇妙な見た目のサンクの型を定義します。
ここでサンクとは、（停止するならば）結果の生成を強制しうる計算を指します。
*)

CoInductive thunk (A : Type) : Type :=
| Answer : A -> thunk A
| Think : thunk A -> thunk A.

(**
(* A computation is either an immediate [Answer] or another computation wrapped inside [Think].  Since [thunk] is co-inductive, every [thunk] type is inhabited by an infinite nesting of [Think]s, standing for non-termination.  Terminating results are [Answer] wrapped inside some finite number of [Think]s.*)

計算は、すぐに[Answer]になるか、[Think]で包まれて別の計算になるか、いずれかです。
[thunk]は余帰納的なので、どの[thunk]型にも、非停止性を表す[Think]の無限の入れ子が含まれています。
停止する結果は、ある有限の個数の[Think]に包まれた[Answer]です。

(* Why bother to write such a strange definition?  The definition of [thunk] is motivated by the ability it gives us to define a "bind" operation, similar to the one we defined in the previous section. *)

わざわざこのように奇妙な定義を書くのはなぜでしょうか。
[thunk]が上記のような定義になっているのは、前節で定義したモナドのbind操作に似たものを定義できるようにするためです。
*)

CoFixpoint TBind A B (m1 : thunk A) (m2 : A -> thunk B) : thunk B :=
  match m1 with
    | Answer x => m2 x
    | Think m1' => Think (TBind m1' m2)
  end.

(**
(* Note that the definition would violate the co-recursion guardedness restriction if we left out the seemingly superfluous [Think] on the righthand side of the second [match] branch.*)

この定義で、[match]の二つめの分岐で右辺の[Think]を省いてしまうと、余再帰のガードに関する制限に違反することに注意してください。

(*   We can prove that [Answer] and [TBind] form a monad for [thunk].  The proof is omitted here but present in the book source.  As usual for this sort of proof, a key element is choosing an appropriate notion of equality for [thunk]s. *)

[Answer]と[TBind]が[thunk]に対するモナドになっていることを証明できます（紙面では証明を省きます）。
いつものように、この手の証明で鍵となるのは、[thunk]についての適切な等価性を選ぶところです。
*)

(* begin hide *)
CoInductive thunk_eq A : thunk A -> thunk A -> Prop :=
| EqAnswer : forall x, thunk_eq (Answer x) (Answer x)
| EqThinkL : forall m1 m2, thunk_eq m1 m2 -> thunk_eq (Think m1) m2
| EqThinkR : forall m1 m2, thunk_eq m1 m2 -> thunk_eq m1 (Think m2).

Section thunk_eq_coind.
  Variable A : Type.
  Variable P : thunk A -> thunk A -> Prop.

  Hypothesis H : forall m1 m2, P m1 m2
    -> match m1, m2 with
         | Answer x1, Answer x2 => x1 = x2
         | Think m1', Think m2' => P m1' m2'
         | Think m1', _ => P m1' m2
         | _, Think m2' => P m1 m2'
       end.

  Theorem thunk_eq_coind : forall m1 m2, P m1 m2 -> thunk_eq m1 m2.
    cofix thunk_eq_coind; intros;
      match goal with
        | [ H' : P _ _ |- _ ] => specialize (H H'); clear H'
      end; destruct m1; destruct m2; subst; repeat constructor; auto.
  Qed.
End thunk_eq_coind.
(* end hide *)

(**
(* In the proofs to follow, we will need a function similar to one we saw in Chapter 5, to pull apart and reassemble a [thunk] in a way that provokes reduction of co-recursive calls. *)

以降の証明では、余再帰呼び出しの簡約を引き起こすような形で[thunk]を解体して再構成するために、第5章で見たような関数が必要です。
*)

Definition frob A (m : thunk A) : thunk A :=
  match m with
    | Answer x => Answer x
    | Think m' => Think m'
  end.

Theorem frob_eq : forall A (m : thunk A), frob m = m.
  destruct m; reflexivity.
Qed.

(* begin hide *)
Theorem thunk_eq_frob : forall A (m1 m2 : thunk A),
  thunk_eq (frob m1) (frob m2)
  -> thunk_eq m1 m2.
  intros; repeat rewrite frob_eq in *; auto.
Qed.

Ltac findDestr := match goal with
                    | [ |- context[match ?E with Answer _ => _ | Think _ => _ end] ] =>
                      match E with
                        | context[match _ with Answer _ => _ | Think _ => _ end] => fail 1
                        | _ => destruct E
                      end
                  end.

Theorem thunk_eq_refl : forall A (m : thunk A), thunk_eq m m.
  intros; apply (thunk_eq_coind (fun m1 m2 => m1 = m2)); crush; findDestr; reflexivity.
Qed.

Hint Resolve thunk_eq_refl.

Theorem tleft_identity : forall A B (a : A) (f : A -> thunk B),
  thunk_eq (TBind (Answer a) f) (f a).
  intros; apply thunk_eq_frob; crush.
Qed.

Theorem tright_identity : forall A (m : thunk A),
  thunk_eq (TBind m (@Answer _)) m.
  intros; apply (thunk_eq_coind (fun m1 m2 => m1 = TBind m2 (@Answer _))); crush;
    findDestr; reflexivity.
Qed.

Lemma TBind_Answer : forall (A B : Type) (v : A) (m2 : A -> thunk B),
  TBind (Answer v) m2 = m2 v.
  intros; rewrite <- (frob_eq (TBind (Answer v) m2));
    simpl; findDestr; reflexivity.
Qed.

Hint Rewrite TBind_Answer.

(** printing exists $\exists$ *)

Theorem tassociativity : forall A B C (m : thunk A) (f : A -> thunk B) (g : B -> thunk C),
  thunk_eq (TBind (TBind m f) g) (TBind m (fun x => TBind (f x) g)).
  intros; apply (thunk_eq_coind (fun m1 m2 => (exists m,
    m1 = TBind (TBind m f) g
    /\ m2 = TBind m (fun x => TBind (f x) g))
  \/ m1 = m2)); crush; eauto; repeat (findDestr; crush; eauto).
Qed.
(* end hide *)

(**
(* As a simple example, here is how we might define a tail-recursive factorial function. *)

簡単な例として、末尾再帰の階乗関数を定義する方法を考えてみましょう。
*)

CoFixpoint fact (n acc : nat) : thunk nat :=
  match n with
    | O => Answer acc
    | S n' => Think (fact n' (S n' * acc))
  end.

(**
(* To test our definition, we need an evaluation relation that characterizes results of evaluating [thunk]s. *)

この定義を試してみるには、[thunk]の評価の結果を特徴付ける評価関係が必要です。
*)

Inductive eval A : thunk A -> A -> Prop :=
| EvalAnswer : forall x, eval (Answer x) x
| EvalThink : forall m x, eval m x -> eval (Think m) x.

Hint Rewrite frob_eq.

Lemma eval_frob : forall A (c : thunk A) x,
  eval (frob c) x
  -> eval c x.
  crush.
Qed.

Theorem eval_fact : eval (fact 5 1) 120.
  repeat (apply eval_frob; simpl; constructor).
Qed.

(**
(* We need to apply constructors of [eval] explicitly, but the process is easy to automate completely for concrete input programs. *)

[eval]の構成子を明示的に適用する必要がありますが、具体的なプログラムに対しては簡単に自動化できます。
*)


(* Now consider another very similar definition, this time of a Fibonacci number function. *)

よく似た別の定義も見てみましょう。今度の例はフィボナッチ数を生成する関数です。
*)

Notation "x <- m1 ; m2" :=
  (TBind m1 (fun x => m2)) (right associativity, at level 70).

(* begin hide *)
(* begin thide *)
Definition fib := pred.
(* end thide *)
(* end hide *)

(** [[
CoFixpoint fib (n : nat) : thunk nat :=
  match n with
    | 0 => Answer 1
    | 1 => Answer 1
    | _ => n1 <- fib (pred n);
      n2 <- fib (pred (pred n));
      Answer (n1 + n2)
  end.
]]


(* Coq complains that the guardedness condition is violated.  The two recursive calls are immediate arguments to [TBind], but [TBind] is not a constructor of [thunk].  Rather, it is a defined function.  This example shows a very serious limitation of [thunk] for traditional functional programming: it is not, in general, possible to make recursive calls and then make further recursive calls, depending on the first call's result.  The [fact] example succeeded because it was already tail recursive, meaning no further computation is needed after a recursive call. *)

この定義は、Coqにより、ガード条件に違反しているとみなされます。
[fib]の再帰呼び出しは、すぐに[TBind]の引数になりますが、[TBind]は[thunk]の構成子ではありません。むしろ[TBind]は定義された関数です。
この例からは、従来の関数プログラミングと比べて、[thunk]には深刻な制限があることがわかります。
その制限とは、再帰呼び出しに続けてさらに再帰呼び出しをすることが一般にはできないことです。最初の再帰呼び出しの結果によって、可能かどうかが変わります。
[fact]の例がうまくいったは、末尾再帰になっていて、再帰呼び出しの後にさらに計算が必要ないからでした。

(* I know no easy fix for this problem of [thunk], but we can define an alternate co-inductive monad that avoids the problem, based on a proposal by Megacz%~\cite{Megacz}%.  We ran into trouble because [TBind] was not a constructor of [thunk], so let us define a new type family where "bind" is a constructor. *)

この[thunk]の制限については、簡単な解決策はわかっていませんが、代わりに余帰納モナドを定義して回避するというMegacz%~\cite{Megacz}%の提案に基づく方法が知られています。
問題になるのは[TBind]が[thunk]の構成子ではないことだったので、bind操作を構成子として持つような型族を新たに定義しましょう。
*)

CoInductive comp (A : Type) : Type :=
| Ret : A -> comp A
| Bnd : forall B, comp B -> (B -> comp A) -> comp A.

(**
(* This example shows off Coq's support for%\index{recursively non-uniform parameters}% _recursively non-uniform parameters_, as in the case of the parameter [A] declared above, where each constructor's type ends in [comp A], but there is a recursive use of [comp] with a different parameter [B].  Beside that technical wrinkle, we see the simplest possible definition of a monad, via a type whose two constructors are precisely the monad operators. *)

この例からは、Coqが%\index{異なる変数に対する再帰}% _{異なる変数に対する再帰}_に対応していることがわかります。
具体的には、上記の宣言では変数[A]に対する場合分けをしており、各構成子の型の最後が[comp A]になっていますが、別の変数[B]でも[comp]を再帰的に使っています。
この点で技術的には目新しさがありますが、二つの構成子がそのままモナドの演算子になっているという意味で、これ以上ないくらい簡潔なモナドの定義になっています。

(* It is easy to define the semantics of terminating [comp] computations. *)

[comp]の計算の停止性に対するセマンティクスは簡単に定義できます。
*)

Inductive exec A : comp A -> A -> Prop :=
| ExecRet : forall x, exec (Ret x) x
| ExecBnd : forall B (c : comp B) (f : B -> comp A) x1 x2, exec (A := B) c x1
  -> exec (f x1) x2
  -> exec (Bnd c f) x2.

(**
(* We can also prove that [Ret] and [Bnd] form a monad according to a notion of [comp] equality based on [exec], but we omit details here; they are in the book source at this point. *)

[comp]の等価性を[exec]の結果に応じて決めれば、[Ret]と[Bnd]がモナドを形成することも証明できます（紙面では詳細は割愛します）。
*)

(* begin hide *)
Hint Constructors exec.

Definition comp_eq A (c1 c2 : comp A) := forall r, exec c1 r <-> exec c2 r.

Ltac inverter := repeat match goal with
                          | [ H : exec _ _ |- _ ] => inversion H; []; crush
                        end.

Theorem cleft_identity : forall A B (a : A) (f : A -> comp B),
  comp_eq (Bnd (Ret a) f) (f a).
  red; crush; inverter; eauto.
Qed.

Theorem cright_identity : forall A (m : comp A),
  comp_eq (Bnd m (@Ret _)) m.
  red; crush; inverter; eauto.
Qed.

Lemma cassociativity1 : forall A B C (f : A -> comp B) (g : B -> comp C) r c,
  exec c r
  -> forall m, c = Bnd (Bnd m f) g
   -> exec (Bnd m (fun x => Bnd (f x) g)) r.
  induction 1; crush.
  match goal with
    | [ H : Bnd _ _ = Bnd _ _ |- _ ] => injection H; clear H; intros; try subst
  end.
  try subst B. (* This line expected to fail in Coq 8.4 and succeed in Coq 8.6. *)
  crush.
  inversion H; clear H; crush.
  eauto.
Qed.

Lemma cassociativity2 : forall A B C (f : A -> comp B) (g : B -> comp C) r c,
  exec c r
  -> forall m, c = Bnd m (fun x => Bnd (f x) g)
   -> exec (Bnd (Bnd m f) g) r.
  induction 1; crush.
  match goal with
    | [ H : Bnd _ _ = Bnd _ _ |- _ ] => injection H; clear H; intros; try subst
  end.
  try subst A. (* Same as above *)
  crush.
  inversion H0; clear H0; crush.
  eauto.
Qed.

Hint Resolve cassociativity1 cassociativity2.

Theorem cassociativity : forall A B C (m : comp A) (f : A -> comp B) (g : B -> comp C),
  comp_eq (Bnd (Bnd m f) g) (Bnd m (fun x => Bnd (f x) g)).
  red; crush; eauto.
Qed.
(* end hide *)

(**
(* Not only can we define the Fibonacci function with the new monad, but even our running example of merge sort becomes definable.  By shadowing our previous notation for "bind," we can write almost exactly the same code as in our previous [mergeSort'] definition, but with less syntactic clutter. *)

このモナドで定義できるのはフィボナッチ関数だけではありません。マージソートも定義可能です。
bind操作に対する以前の記法を隠すことで、先の[mergeSort']の定義とほとんど同じコードを、よりすっきりとしたシンタックスで書けます。
*)

Notation "x <- m1 ; m2" := (Bnd m1 (fun x => m2)).

CoFixpoint mergeSort'' A (le : A -> A -> bool) (ls : list A) : comp (list A) :=
  if le_lt_dec 2 (length ls)
    then let lss := split ls in
      ls1 <- mergeSort'' le (fst lss);
      ls2 <- mergeSort'' le (snd lss);
      Ret (merge le ls1 ls2)
    else Ret ls.

(**
(* To execute this function, we go through the usual exercise of writing a function to catalyze evaluation of co-recursive calls. *)

この関数を実行するには、いつものように、余再帰呼び出しの評価に対して触媒となる関数を書きます。
*)

Definition frob' A (c : comp A) :=
  match c with
    | Ret x => Ret x
    | Bnd _ c' f => Bnd c' f
  end.

Lemma exec_frob : forall A (c : comp A) x,
  exec (frob' c) x
  -> exec c x.
  destruct c; crush.
Qed.

(**
(* Now the same sort of proof script that we applied for testing [thunk]s will get the job done. *)

あとは、[thunk]のテストで適用した証明スクリプトと同様にするだけです。
*)

Lemma test_mergeSort'' : exec (mergeSort'' leb (1 :: 2 :: 36 :: 8 :: 19 :: nil))
  (1 :: 2 :: 8 :: 19 :: 36 :: nil).
  repeat (apply exec_frob; simpl; econstructor).
Qed.

(**
(* Have we finally reached the ideal solution for encoding general recursive definitions, with minimal hassle in syntax and proof obligations?  Unfortunately, we have not, as [comp] has a serious expressivity weakness.  Consider the following definition of a curried addition function: *)

これで、シンタックスやproof obligationになるべく煩わされずに一般再帰の定義をエンコードする、理想的な方法に行きついたでしょうか。
残念ながら行きついていません。[comp]には表現性の面で大きな弱点があるからです。
カリー化された加算の関数に対する次のような定義を考えてみてください。
*)

Definition curriedAdd (n : nat) := Ret (fun m : nat => Ret (n + m)).

(**
(* This definition works fine, but we run into trouble when we try to apply it in a trivial way. *)

これは、定義はできるものの、自明な形で適用しようとすると問題が生じます。
[[
Definition testCurriedAdd := Bnd (curriedAdd 2) (fun f => f 3).
]]

<<
Error: Universe inconsistency.
>>

(* The problem has to do with rules for inductive definitions that we will study in more detail in Chapter 12.  Briefly, recall that the type of the constructor [Bnd] quantifies over a type [B].  To make [testCurriedAdd] work, we would need to instantiate [B] as [nat -> comp nat].  However, Coq enforces a %\emph{predicativity restriction}% that (roughly) no quantifier in an inductive or co-inductive type's definition may ever be instantiated with a term that contains the type being defined.  Chapter 12 presents the exact mechanism by which this restriction is enforced, but for now our conclusion is that [comp] is fatally flawed as a way of encoding interesting higher-order functional programs that use general recursion. *)

この問題は、帰納的な定義に対する規則に関係しており、この規則については第12章で詳しく解説します。
簡単に言うと、ここで問題になるのは、構成子[Bnd]の型が[B]で限量されていることです。
[testCurriedAdd]を動かすには、[nat -> comp nat]として[B]をインスタンスする必要があるでしょう。
しかし、Coqには%\emph{可述性の制限}%という規則があり、帰納型や余帰納型の定義における限量子は、定義している型を含む項を使ってインスタンス化されてはいけません（これは厳密な説明ではありません）。
この制限が課される仕組みについては第12章で正確に説明しますが、今のところはっきり言えるのは、一般再帰を利用した高階の面白い関数プログラムをエンコードするには[comp]には致命的な欠点がある、ということです。
*)

(**
(* * Comparing the Alternatives *)

* 各手法の比較
*)

(**
(* We have seen four different approaches to encoding general recursive definitions in Coq.  Among them there is no clear champion that dominates the others in every important way.  Instead, we close the chapter by comparing the techniques along a number of dimensions.  Every technique allows recursive definitions with termination arguments that go beyond Coq's built-in termination checking, so we must turn to subtler points to highlight differences.*)

本章では、Coqで一般再帰の定義をエンコードする四つの技法を見てきました。
四つの技法のいずれにも、それ以外の技法をすべての面で圧倒するような利点はありません。
そこで、本章を締めくくるにあたり、さまざまな側面について各技法を比較してみます。
いずれの技法も、「Coqに組み込みの機構では引数による停止性を確かめられないような再帰的な定義を可能にする」という点では同等です。
したがって、技法による違いを示すため、かなり些細な部分について言及していきます。

(* One useful property is automatic integration with normal Coq programming.  That is, we would like the type of a function to be the same, whether or not that function is defined using an interesting recursion pattern.  Only the first of the four techniques, well-founded recursion, meets this criterion.  It is also the only one of the four to meet the related criterion that evaluation of function calls can take place entirely inside Coq's built-in computation machinery.  The monad inspired by domain theory occupies some middle ground in this dimension, since generally standard computation is enough to evaluate a term once a high enough approximation level is provided. *)

まず気になるのは通常のCoqプログラミングにおける使い勝手です。
関数の型が一般再帰で定義するかどうかによって変わってしまうと、何も考えずに通常のCoqプログラミングと統合するのが難しくなります。
この基準を満たすのは、本章の四つの技法のうち一つめに説明した整礎な再帰による技法だけです。
整礎な再帰による技法は、四つのうちで「関数の呼び出しが起こるのがCoqの組み込みの計算機構の内部だけである」という基準を満たす唯一の技法でもあります。
領域理論を応用したモナドによる技法は、十分に高い近似レベルさえ与えれば標準的な計算だけで通常は項を評価できるので、この点では中庸です。

(*   Another useful property is that a function and its termination argument may be developed separately.  We may even want to define functions that fail to terminate on some or all inputs.  The well-founded recursion technique does not have this property, but the other three do. *)

もうひとつ気になるのは、関数とその停止性を決める引数を別々に開発できるかどうかです。
場合によっては、特定の入力に対して停止しなかったり、すべての入力について停止しない関数を定義したいこともあります。
この性質は、整礎な再帰による技法にはありませんが、他の三つの技法にはあります。

(*   One minor plus is the ability to write recursive definitions in natural syntax, rather than with calls to higher-order combinators.  This downside of the first two techniques is actually rather easy to get around using Coq's notation mechanism, though we leave the details as an exercise for the reader.  (For this and other details of notations, see Chapter 12 of the Coq 8.4 manual.) *)

マイナーな観点として、再帰的な定義を書くのに高階の結合子を呼び出す必要がなく、自然なシンタックスで書けるかどうかも気になります。
この点で本章の前半の二つの技法は劣っていますが、記法に関するCoqの仕組みを使えば比較的容易に対処可能です。
実際にどうすればいいかは本書では割愛します（記法に関するCoqの仕組みについてはCoq 8.4のマニュアルのChapter 12を参照してください）。

(*   The first two techniques impose proof obligations that are more basic than termination arguments, where well-founded recursion requires a proof of extensionality and domain-theoretic recursion requires a proof of continuity.  A function may not be defined, and thus may not be computed with, until these obligations are proved.  The co-inductive techniques avoid this problem, as recursive definitions may be made without any proof obligations. *)

proof obligationを課すということは、引数による停止性の確認に比べて、より基本的な部分に踏み込むということです。
整礎な再帰では関数の外延性に関するproof obligationを課し、領域理論を応用した再帰では継続に関するproof obligationを課しました。
これらのproof obligationが証明されない限り関数は定義されず、それゆえに関数を使った計算も起こりません。
余帰納による技法では、proof obligationなしで再帰的な定義が可能であることから、この問題を回避できます。

(*   We can also consider support for common idioms in functional programming.  For instance, the [thunk] monad effectively only supports recursion that is tail recursion, while the others allow arbitrary recursion schemes.*)

一般的な関数プログラミングのイディオムに対応しているかどうかも気になります。
たとえば、[thunk]モナドは末尾再帰にしか対応していませんが、他の技法は任意の種類の再帰に対応しています。

(*   On the other hand, the [comp] monad does not support the effective mixing of higher-order functions and general recursion, while all the other techniques do.  For instance, we can finish the failed [curriedAdd] example in the domain-theoretic monad. *)

また、[comp]モナド以外の技法では、高階関数と一般再帰を効果的に組み合わせることが可能です。
たとえば、前節でうまくいかなかった[curriedAdd]の定義は、領域理論を応用した技法では次のようにして完遂できます。
*)

Definition curriedAdd' (n : nat) := Return (fun m : nat => Return (n + m)).

Definition testCurriedAdd := Bind (curriedAdd' 2) (fun f => f 3).

(**
(* The same techniques also apply to more interesting higher-order functions like list map, and, as in all four techniques, we can mix primitive and general recursion, preferring the former when possible to avoid proof obligations. *)

同じ技法は、リストに対するmapのような、より興味深い高階関数にも適用できます。
四つの技法のそれぞれの例で見たように、原子再帰と一般再帰を組み合わせて、可能な場合には原子再帰を優先してproof obligationsを回避するようにできます。
*)

Fixpoint map A B (f : A -> computation B) (ls : list A) : computation (list B) :=
  match ls with
    | nil => Return nil
    | x :: ls' => Bind (f x) (fun x' =>
      Bind (map f ls') (fun ls'' =>
        Return (x' :: ls'')))
  end.

(** remove printing exists *)
Theorem test_map : run (map (fun x => Return (S x)) (1 :: 2 :: 3 :: nil))
  (2 :: 3 :: 4 :: nil).
  exists 1; reflexivity.
Qed.

(**
(* One further disadvantage of [comp] is that we cannot prove an inversion lemma for executions of [Bind] without appealing to an _axiom_, a logical complication that we discuss at more length in Chapter 12.  The other three techniques allow proof of all the important theorems within the normal logic of Coq.*)

さらに[comp]には、_[公理]_を利用しなければ[Bind]の実行のための逆転の補題を証明できないという、論理的な難点もあります（詳細は第12章で説明します）。
それ以外の三つの技法は、通常のCoqの論理の内部で、重要な定理をすべて証明できます。

(* Perhaps one theme of our comparison is that one must trade off between, on one hand, functional programming expressiveness and compatibility with normal Coq types and computation; and, on the other hand, the level of proof obligations one is willing to handle at function definition time. *)

四つの技法の比較を通して見えてくるのは、「関数プログラミングの表現力」と「通常のCoqの型および計算との互換性」との間には一種のトレードオフがあるということです。
これは、関数を定義する際に対処しようと思うproof obligationのレベルによる相違だと考えることもできるでしょう。
*)
