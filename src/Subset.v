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

Require Extraction.

Set Implicit Arguments.
Set Asymmetric Patterns.
(* end hide *)

(** printing <-- $\longleftarrow$ *)


(**
(* %\part{Programming with Dependent Types} 

\chapter{Subset Types and Variations}% *)

%\part{依存型によるプログラミング} \chapter{部分集合とその仲間}%


(**
(* So far, we have seen many examples of what we might call "classical program verification."  We write programs, write their specifications, and then prove that the programs satisfy their specifications.  The programs that we have written in Coq have been normal functional programs that we could just as well have written in Haskell or ML.  In this chapter, we start investigating uses of%\index{dependent types}% _dependent types_ to integrate programming, specification, and proving into a single phase.  The techniques we will learn make it possible to reduce the cost of program verification dramatically. *)

第I部では「古典的なプログラム検証」と呼ばれるものの例をいくつも見てきました。
プログラムを書き、その仕様を書いて、それからプログラムが仕様を満たすことを証明しました。
Coqで書いたプログラムは、HaskellやMLで書いていたような通常の関数プログラミングでした。
本章では、プログラミングと仕様と証明を一つの相に統合するために、%\index{依存型}% _依存型_の使い方を見ていきます。

(**
* Introducing Subset Types 

* 部分集合型の導入

(* Let us consider several ways of implementing the natural number predecessor function.  We start by displaying the definition from the standard library: *)

自然数の前者関数を実装する方法をいくつか考えてみましょう。
標準ライブラリにおける定義から始めます。

*)

Print pred.
(** %\vspace{-.15in}% [[
pred = fun n : nat => match n with
                      | 0 => 0
                      | S u => u
                      end
     : nat -> nat
 
]]

(* We can use a new command, %\index{Vernacular commands!Extraction}\index{program extraction}\index{extraction|see{program extraction}}%[Extraction], to produce an %\index{OCaml}%OCaml version of this function. *)

%\index{Vernacular commands!Extraction}\index{program extraction}\index{extraction|see{program extraction}}%
[Extraction]という新しいコマンドを使うと、この関数から、%\index{OCaml}%OCamlの関数を生成できます。

Extraction pred.
(** %\vspace{-.15in}% [[

(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u
]]

(* Returning 0 as the predecessor of 0 can come across as somewhat of a hack.  In some situations, we might like to be sure that we never try to take the predecessor of 0.  We can enforce this by giving [pred] a stronger, dependent type. *)

0の前者として0を返すのは、ある種のハックに思えます。
状況によっては、0の前者を取ろうとすることを一切できなくしたいところです。
これを強制する手法として、依存型と呼ばれる強力な引数を[pred]に持たせるという手があります。
*)

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(**
(* We expand the type of [pred] to include a _proof_ that its argument [n] is greater than 0.  When [n] is 0, we use the proof to derive a contradiction, which we can use to build a value of any type via a vacuous pattern match.  When [n] is a successor, we have no need for the proof and just return the answer.  The proof argument can be said to have a _dependent_ type, because its type depends on the _value_ of the argument [n].

   Coq's [Eval] command can execute particular invocations of [pred_strong1] just as easily as it can execute more traditional functional programs.  Note that Coq has decided that argument [n] of [pred_strong1] can be made _implicit_, since it can be deduced from the type of the second argument, so we need not write [n] in function calls. *)

上記では、[pred]の型を拡張して、「その引数[n]が0より大きい」ことの_証明_を含められるようにしています。
[n]が0の場合には、その証明を使って矛盾を導き、場合分けがないパターンマッチを介して任意の型の値を作り出せます。
[n]が何かの後者である場合には、その証明は必要ないので、単に答えを返します。
証明を引数に取る関数は、その型が引数[n]の_値_に依存するので、_依存型を持つ_と呼ばれます。

Coqで[pred_strong1]を実行するには[Eval]コマンドを使います。一般的な関数プログラムと同じように実行可能です。
[pred_strong1]の引数[n]は、二番めの引数の型から導出できるので、Coqにより「_暗黙_に生成できる」と判断されていることに注目してください。
そのため、関数を呼び出すときに[n]を指定する必要はありません。
*)

Theorem two_gt0 : 2 > 0.
  crush.
Qed.

Eval compute in pred_strong1 two_gt0.
(** [[
     = 1
     : nat
 ]]

(* One aspect in particular of the definition of [pred_strong1] may be surprising.  We took advantage of [Definition]'s syntactic sugar for defining function arguments in the case of [n], but we bound the proofs later with explicit [fun] expressions.  Let us see what happens if we write this function in the way that at first seems most natural. *)

[pred_strong1]の定義には、意外かもしれない点が一つあります。
[n]についての場合分けでは[Definition]の構文糖衣を利用して関数の引数を定義しましたが、わざわざ[fun]式を作って後から証明を束縛しているところです。
次のように書くほうが自然に思えるかもしれません。

[[
Definition pred_strong1' (n : nat) (pf : n > 0) : nat :=
  match n with
    | O => match zgtz pf with end
    | S n' => n'
  end.
]]

<<
Error: In environment
n : nat
pf : n > 0
The term "pf" has type "n > 0" while it is expected to have type 
"0 > 0"
>>

(* The term [zgtz pf] fails to type-check.  Somehow the type checker has failed to take into account information that follows from which [match] branch that term appears in.  The problem is that, by default, [match] does not let us use such implied information.  To get refined typing, we must always rely on [match] annotations, either written explicitly or inferred. *)

[zgtz pf]という項は型検査に失敗します。
どういうわけか、この項が出現する[match]節から得られるはずの情報を加味することに、型検査器が失敗してしまうのです。
問題は、[match]ではこのような暗黙の情報をデフォルトでは使えないことにあります。
型付けの精度を上げるには、明示的なものであれ推論されるものであれ、[match]に対する注釈に頼る必要があります。

(* In this case, we must use a [return] annotation to declare the relationship between the _value_ of the [match] discriminee and the _type_ of the result.  There is no annotation that lets us declare a relationship between the discriminee and the type of a variable that is already in scope; hence, we delay the binding of [pf], so that we can use the [return] annotation to express the needed relationship. *)

この場合は、[match]の判定に使われる_値_と結果の_型_との間に関係があることを宣言する必要があり、そのために[return]という注釈を使っています。
スコープ内にある変数の型が判定に使われる値に関係していることを宣言する注釈はないので、必要になる関係を[return]で表現できるように、[pf]の束縛を遅らせているのです。

(* We are lucky that Coq's heuristics infer the [return] clause (specifically, [return n > 0 -> nat]) for us in the definition of [pred_strong1], leading to the following elaborated code: *)

幸い、[pred_strong1]の定義における[return]節（具体的には[return n > 0 -> nat]）ではCoqのヒューリスティックによる推論が効くので、下記のように簡潔に書くことはできます。
*)

Definition pred_strong1' (n : nat) : n > 0 -> nat :=
  match n return n > 0 -> nat with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

(** 
(* By making explicit the functional relationship between value [n] and the result type of the [match], we guide Coq toward proper type checking.  The clause for this example follows by simple copying of the original annotation on the definition.  In general, however, the [match] annotation inference problem is undecidable.  The known undecidable problem of%\index{higher-order unification}% _higher-order unification_ %\cite{HOU}% reduces to the [match] type inference problem.  Over time, Coq is enhanced with more and more heuristics to get around this problem, but there must always exist [match]es whose types Coq cannot infer without annotations. *)

値[n]と、[match]の結果の型との間の関係を明示することで、Coqが適切に型検査をするように誘導できます。
注釈としては、この例では標準ライブラリの定義にあるものを引き写しましたが、[match]に対する注釈を決めるという問題は一般には決定不能です。
[match]の型を推論する問題は、%\index{高階ユニフィケーション}% _高階ユニフィケーション_ %\cite{HOU}%（higher-order unification）と呼ばれる問題に帰着します。
長年の間にヒューリスティックにより解決できる範囲は広がりましたが、注釈なしではCodが推論できない[match]の型は必ず残ってしまいます。

(* Let us now take a look at the OCaml code Coq generates for [pred_strong1]. *)

次は、[pred_strong1]に対してCoqが生成するOCamlのコードを見てみましょう。
*)

Extraction pred_strong1.

(** 
<<
(** val pred_strong1 : nat -> nat **)

let pred_strong1 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
>>
*)

(** 
(* The proof argument has disappeared!  We get exactly the OCaml code we would have written manually.  This is our first demonstration of the main technically interesting feature of Coq program extraction: proofs are erased systematically. *)

OCamlのコードでは証明の引数が消えています。
最初からOCamlで書いたかのようなコードが得られました。
Coqによるプログラム抽出が技術的に面白い点は、このように証明がシステマティックに消されることにあります。

(* We can reimplement our dependently typed [pred] based on%\index{subset types}% _subset types_, defined in the standard library with the type family %\index{Gallina terms!sig}%[sig]. *)

依存型を使った[pred]の実装を見ましたが、%\index{subset types}% _部分集合型_（subset type）を使った実装も可能です。
部分集合型は、標準ライブラリでは%\index{Gallina terms!sig}%[sig]という型族で定義されています。
*)

(* begin hide *)
(* begin thide *)
Definition bar := ex.
(* end thide *)
(* end hide *)

Print sig.
(** [[
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P
]]

(* 8.12の出力では`P x -> sig P`ではなく、この段階で`P x -> {x : A | P x}`で表示されてしまう -kshikano *)

(* The family [sig] is a Curry-Howard twin of [ex], except that [sig] is in [Type], while [ex] is in [Prop].  That means that [sig] values can survive extraction, while [ex] proofs will always be erased.  The actual details of extraction of [sig]s are more subtle, as we will see shortly. *)

[Type]である[sig]は、[Prop]である[ex]に対するCurry-Howard対応です。
これは、プログラム抽出では[sig]の値が残り、[ex]の証明が消去されることを意味します。
[sig]の抽出には、後で説明するように、実際に詳しく見るともう少し微妙な点があります。

(* We rewrite [pred_strong1], using some syntactic sugar for subset types. *)

部分集合型には次のような構文糖衣があります。
*)

Locate "{ _ : _ | _ }".
(** [[
  Notation
  "{ x : A  |  P }" := sig (fun x : A => P)
   ]]

これを使って[pred_strong1]を書き換えると、次のようになります。
*)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist O pf => match zgtz pf with end
    | exist (S n') _ => n'
  end.

(**
(* To build a value of a subset type, we use the [exist] constructor, and the details of how to do that follow from the output of our earlier [Print sig] command, where we elided the extra information that parameter [A] is implicit.  We need an extra [_] here and not in the definition of [pred_strong2] because _parameters_ of inductive types (like the predicate [P] for [sig]) are not mentioned in pattern matching, but _are_ mentioned in construction of terms (if they are not marked as implicit arguments). *)

部分集合型の値を組み立てるには[exist]構成子を使います。
どうやって構成するかは、先に示した[Print sig]コマンドの出力から従います。
上記の定義では、[A]型の変数[x]が暗黙に全称限量化されているという情報が省かれていますが、[pred_strong2]を使うときには余分な[_]が必要です。
これは、パターンマッチの中では帰納型の_変数_（[sig]に対する命題[P]など）は言及されませんが、項の構成では実際に言及されるからです
（暗黙の引数であるという注釈があるときは別です）。
*)

Eval compute in pred_strong2 (exist _ 2 two_gt0).
(**  [[
     = 1
     : nat
     ]]
     *)

Extraction pred_strong2.

(**
<<
(** val pred_strong2 : nat -> nat **)

let pred_strong2 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
>>

(* We arrive at the same OCaml code as was extracted from [pred_strong1], which may seem surprising at first.  The reason is that a value of [sig] is a pair of two pieces, a value and a proof about it.  Extraction erases the proof, which reduces the constructor [exist] of [sig] to taking just a single argument.  An optimization eliminates uses of datatypes with single constructors taking single arguments, and we arrive back where we started. *)

OCamlプログラムを抽出してみると、最初は意外に感じるかもしれませんが、上記のように[pred_strong1]の場合と同じコードが得られます。
同じコードが得られる理由は、[sig]の値が、実際には値とその証明の二つから成り立っているからです。
プログラム抽出により、証明は除去され、[sig]の[exist]は引数を一つだけ取るように縮退されます。
最適化により、一つだけ引数を取る単一の構成子からなるデータ型は取り除かれるので、結果として振り出しに戻るのです。

(* We can continue on in the process of refining [pred]'s type.  Let us change its result type to capture that the output is really the predecessor of the input. *)

[pred]の型はさらに洗練できます。
結果の型を変更して、出力が実際に入力の前者であるという事実を捉えたものにしてみましょう。

*)

Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
    | exist 0 pf => match zgtz pf with end
    | exist (S n') pf => exist _ n' (eq_refl _)
  end.

(* begin hide *)
(* begin thide *)
Definition ugh := lt.
(* end thide *)
(* end hide *)

Eval compute in pred_strong3 (exist _ 2 two_gt0).
(**  [[
     = exist (fun m : nat => 2 = S m) 1 (eq_refl 2)
     : {m : nat | proj1_sig (exist (lt 0) 2 two_gt0) = S m}
      ]]
*)

(* begin hide *)
(* begin thide *)
Definition pred_strong := 0.
(* end thide *)
(* end hide *)

(**
(* A value in a subset type can be thought of as a%\index{dependent pair}% _dependent pair_ (or%\index{sigma type}% _sigma type_) of a base value and a proof about it.  The function %\index{Gallina terms!proj1\_sig}%[proj1_sig] extracts the first component of the pair.  It turns out that we need to include an explicit [return] clause here, since Coq's heuristics are not smart enough to propagate the result type that we wrote earlier. *)

部分集合型の値は、基になる値とその証明からなる%\index{依存対}% _依存対_（dependent pair）と考えられます。
依存対は、%\index{シグマ型}% _シグマ型_（sigma type）と呼ばれることもあります。
%\index{Gallina terms!proj1\_sig}%[proj1_sig]関数から抽出されるのは、この依存対のうちの一つめの構成要素です。
Coqのヒューリスティックは、先に書いた結果の型が伝わるほどには賢くないので、ここでは明示的な[return]が必要です。

(* By now, the reader is probably ready to believe that the new [pred_strong] leads to the same OCaml code as we have seen several times so far, and Coq does not disappoint. *)

この新しいバージョンの[pred_strong]からも、これまでの例から期待されるとおり、今までと同一のOCamlコードが得られます。
*)

Extraction pred_strong3.

(**
<<
(** val pred_strong3 : nat -> nat **)

let pred_strong3 = function
  | O -> assert false (* absurd case *)
  | S n' -> n'
>>

(* We have managed to reach a type that is, in a formal sense, the most expressive possible for [pred].  Any other implementation of the same type must have the same input-output behavior.  However, there is still room for improvement in making this kind of code easier to write.  Here is a version that takes advantage of tactic-based theorem proving.  We switch back to passing a separate proof argument instead of using a subset type for the function's input, because this leads to cleaner code.  (Recall that [False_rec] is the [Set]-level induction principle for [False], which can be used to produce a value in any [Set] given a proof of [False].) *)

[pred]については、形式的な意味で、考えられる限りもっとも表現力がある型にたどり着きました。
同じ型の他の実装は、入出力に対する挙動がすべて同じでなければなりません。
しかし、コードを書きやすくするという方向では、まだ改善の余地があります。
以下に示すのは、タクティクを使う定理証明を利用したバージョンです。
関数に対する入力として部分集合型を使う代わりに、証明を別の引数で渡すスタイルに戻してコードを見やすくしています。
（[False_rec]は、[Set]における[False]のための帰納法の原理です。[False]の証明を与えられると、任意の[Set]の値を生成します。）
*)

Definition pred_strong4 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end).

(* begin thide *)

(**
(* We build [pred_strong4] using tactic-based proving, beginning with a [Definition] command that ends in a period before a definition is given.  Such a command enters the interactive proving mode, with the type given for the new identifier as our proof goal.  It may seem strange to change perspective so implicitly between programming and proving, but recall that programs and proofs are two sides of the same coin in Coq, thanks to the Curry-Howard correspondence. *)

[pred_strong4]では、タクティクを使った証明を利用して定義を構築するため、定義を与える前にピリオドにより終了する形の[Definition]コマンドから開始しています。
このようにコマンドとして[Definition]を使うと、対話証明モードに入り、新しい識別子には証明のゴールとして型が与えられます。
暗黙のうちにプログラミングと証明に対する見方が入れ替わっていることにので奇妙に思えるかもしれませんが、CoqではCurry-Howard対応によってプログラムと証明は表裏一体であることを思い出しましょう。

(* We do most of the work with the %\index{tactics!refine}%[refine] tactic, to which we pass a partial "proof" of the type we are trying to prove.  There may be some pieces left to fill in, indicated by underscores.  Any underscore that Coq cannot reconstruct with type inference is added as a proof subgoal.  In this case, we have two subgoals: *)

上記では、型に対してこれから試みる「証明」の一部を%\index{tactics!refine}%[refine]に与えています。
アンダースコア（[_]）にした箇所のうちいくつかは、埋めてあげる必要があるでしょう。
Coqが型推論で構成できないアンダースコアは、すべて証明のサブゴールとして提示されます。
この例では二つのサブゴールが提示されます。

[[
2 subgoals
  
  n : nat
  _ : 0 > 0
  ============================
   False

subgoal 2 is

 S n' = S n'
]]

(* We can see that the first subgoal comes from the second underscore passed to [False_rec], and the second subgoal comes from the second underscore passed to [exist].  In the first case, we see that, though we bound the proof variable with an underscore, it is still available in our proof context.  It is hard to refer to underscore-named variables in manual proofs, but automation makes short work of them.  Both subgoals are easy to discharge that way, so let us back up and ask to prove all subgoals automatically. *)

一つめのサブゴールは[False_rec]に渡している二つめのアンダースコアによるものであり、二つめのサブゴールは[exist]に渡している二つめのアンダースコアによるものです。
前者については、証明を表す変数の束縛にアンダースコアを使っていますが、このように証明の文脈でアンダースコアを利用すること自体は可能です。
変数の命名にアンダースコアを使うと、手作業の証明では参照が難しくなりますが、自動化がうまく対処してくれます。
どちらのサブゴールも容易に対処できるものなので、巻き戻してすべてのサブゴールを自動で証明するように指示しましょう。

*)

  Undo.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end); crush.
(* end thide *)
Defined.

(**
(* We end the "proof" with %\index{Vernacular commands!Defined}%[Defined] instead of [Qed], so that the definition we constructed remains visible.  This contrasts to the case of ending a proof with [Qed], where the details of the proof are hidden afterward.  (More formally, [Defined] marks an identifier as%\index{transparent}% _transparent_, allowing it to be unfolded; while [Qed] marks an identifier as%\index{opaque}% _opaque_, preventing unfolding.)  Let us see what our proof script constructed. *)

この「証明」を終えるときは、[Qed]ではなく%\index{Vernacular commands!Defined}%[Defined]を使いました。
[Defined]では、構成した定義が引き続き見える状態になります。
一方、[Qed]で証明を終えると、以降は証明の詳細が隠蔽されます。
（より形式的に言うと、[Defined]は識別子に対して%\index{透明}% _透明_（transparent）であるという印を付けて展開可能にし、
[Qed]は%\index{不透明}% _不透明_（opaque）という印を付けて展開できなくします。）
*)

Print pred_strong4.
(** [[
pred_strong4 = 
fun n : nat =>
match n as n0 return (n0 > 0 -> {m : nat | n0 = S m}) with
| 0 =>
    fun _ : 0 > 0 =>
    False_rec {m : nat | 0 = S m}
      (Bool.diff_false_true
         (Bool.absurd_eq_true false
            (Bool.diff_false_true
               (Bool.absurd_eq_true false (pred_strong4_subproof n _)))))
| S n' =>
    fun _ : S n' > 0 =>
    exist (fun m : nat => S n' = S m) n' (eq_refl (S n'))
end
     : forall n : nat, n > 0 -> {m : nat | n = S m}
]]

(* We see the code we entered, with some proofs filled in.  The first proof obligation, the second argument to [False_rec], is filled in with a nasty-looking proof term that we can be glad we did not enter by hand.  The second proof obligation is a simple reflexivity proof. *)

入力したコードに、いくつか証明が補完されていることがわかります。
最初のサブゴールに対応する、[False_rec]の二つめの引数に入る「証明すべき責務」（proof obligation）は、とても手作業で入力する気にはならない醜悪な見た目の証明項で埋められています。
もう一つのproof obligationである[exist]の二つめの引数には、反射性に関する単純な証明が入っています。
*)

Eval compute in pred_strong4 two_gt0.
(**  [[
     = exist (fun m : nat => 2 = S m) 1 (eq_refl 2)
     : {m : nat | 2 = S m}
     ]]

(* A tactic modifier called %\index{tactics!abstract}%[abstract] can be helpful for producing shorter terms, by automatically abstracting subgoals into named lemmas. *)

サブゴールを自動的に抽象化して名前付きの補題にしてくれる、%\index{tactics!abstract}%[abstract]という便利なタクティク変更の仕組みもあります。
*)

(* begin thide *)
Definition pred_strong4' : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end); abstract crush.
Defined.

Print pred_strong4'.
(* end thide *)

(**  [[
pred_strong4' = 
fun n : nat =>
match n as n0 return (n0 > 0 -> {m : nat | n0 = S m}) with
| 0 =>
    fun _H : 0 > 0 =>
    False_rec {m : nat | 0 = S m} (pred_strong4'_subproof n _H)
| S n' =>
    fun _H : S n' > 0 =>
    exist (fun m : nat => S n' = S m) n' (pred_strong4'_subproof0 n _H)
end
     : forall n : nat, n > 0 -> {m : nat | n = S m}
]]

(* We are almost done with the ideal implementation of dependent predecessor.  We can use Coq's syntax extension facility to arrive at code with almost no complexity beyond a Haskell or ML program with a complete specification in a comment.  In this book, we will not dwell on the details of syntax extensions; the Coq manual gives a straightforward introduction to them. *)

依存型による前者関数の理想的な実装まで、あと一歩です。
Coqにはシンタックスを拡張する機能があり、その機能を使えば、完全な仕様をコメントに含めたうえで、HaskellやMLのプログラムと比べても複雑さで見劣りがしないコードにできます。
シンタックスの拡張について本書では詳しく触れませんが、Coqのマニュアルを見れば一目瞭然でしょう。
*)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.

(**
(* By default, notations are also used in pretty-printing terms, including results of evaluation. *)

[Notation]の設定は、評価結果を含め、項のプリティプリントにもデフォルトで使われます。
*)

Eval compute in pred_strong5 two_gt0.
(** %\vspace{-.15in}% [[
     = [1]
     : {m : nat | 2 = S m}
     ]]

(*  One other alternative is worth demonstrating.  Recent Coq versions include a facility called %\index{Program}%[Program] that streamlines this style of definition.  Here is a complete implementation using [Program].%\index{Vernacular commands!Obligation Tactic}\index{Vernacular commands!Program Definition}% *)

もう一つ、説明しておくべきことがあります。
Coqの比較的新しい機能として、ここで説明したスタイルでの定義を簡潔にできるようになる、%\index{Program}%[Program]という仕組みがあります。
[Program]を使った完全な実装は次のようになります。%\index{Vernacular commands!Obligation Tactic}\index{Vernacular commands!Program Definition}%
*)

Obligation Tactic := crush.

Program Definition pred_strong6 (n : nat) (_ : n > 0) : {m : nat | n = S m} :=
  match n with
    | O => _
    | S n' => n'
  end.

(**
(* Printing the resulting definition of [pred_strong6] yields a term very similar to what we built with [refine].  [Program] can save time in writing programs that use subset types.  Nonetheless, [refine] is often just as effective, and [refine] gives more control over the form the final term takes, which can be useful when you want to prove additional theorems about your definition.  [Program] will sometimes insert type casts that can complicate theorem proving. *)

[pred_strong6]による定義の結果を出力してみると、[refine]で組み立てた結果によく似た項が得られます。
[Program]は、部分集合型を使ったプログラムを書く時間を節約してくれます。
にもかかわらず、[refine]は十分に効率的であり、最終的な項の形もそれなりに自由に制御できるので、証明する定義に関連した定理をほかにも証明したい場合には都合がいいでしょう。
[Program]は、定理の証明を複雑にする型キャストを挿入する場合もあります。
*)

Eval compute in pred_strong6 two_gt0.
(** %\vspace{-.15in}% [[
     = [1]
     : {m : nat | 2 = S m}
     ]]

(* In this case, we see that the new definition yields the same computational behavior as before. *)

この場合には、[Program]による定義でも、計算的な振る舞いは今までと同じになることがわかりました。
*)

(**
(* Decidable Proposition Types *)

決定可能な命題の型
*)

(**
(* There is another type in the standard library that captures the idea of program values that indicate which of two propositions is true.%\index{Gallina terms!sumbool}% *)

「二つの命題のうちどちらが真か」は、プログラムの値として指し示せます。そのような値の型が

%\index{Gallina terms!sumbool}%
*)

Print sumbool.
(** %\vspace{-.15in}% [[
Inductive sumbool (A : Prop) (B : Prop) : Set :=
    left : A -> {A} + {B} | right : B -> {A} + {B}
]]

(* Here, the constructors of [sumbool] have types written in terms of a registered notation for [sumbool], such that the result type of each constructor desugars to [sumbool A B].  We can define some notations of our own to make working with [sumbool] more convenient. *)

[sumbool]の構成子である[left]および[right]は、[sumbool]用に予約されている表記であり、それぞれの構成子の結果の型は、構文糖衣を展開すると[sumbool A B]になります。
もっと使いやすい別の表記を定義してもかまいません。
*)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

(**
(* The %\coqdocnotation{%#<tt>#Reduce#</tt>#%}% notation is notable because it demonstrates how [if] is overloaded in Coq.  The [if] form actually works when the test expression has any two-constructor inductive type.  Moreover, in the [then] and [else] branches, the appropriate constructor arguments are bound.  This is important when working with [sumbool]s, when we want to have the proof stored in the test expression available when proving the proof obligations generated in the appropriate branch. *)

%\coqdocnotation{%#<tt>#Reduce#</tt>#%}%は、Coqにおいて[if]をオーバーロードする方法の一例として注目に値します。
[Reduce]では、[if]形式が条件式として構成子を二つ持つような任意の帰納型を取ります。
そして、その構成子のうち適切なほうが[then]節および[else]節で束縛されます。
[sumbool]を扱っていて、いずれかの節で生成されるproof obligationの証明に際して条件式に格納された証明を利用したいときは、この束縛が重要になります。

(* Now we can write [eq_nat_dec], which compares two natural numbers, returning either a proof of their equality or a proof of their inequality. *)

二つの自然数を比較し、それらが等価であることの証明、もしくは不等価であることの証明を返す[eq_nat_dec]を定義してみましょう。
*)

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
    match n, m with
      | O, O => Yes
      | S n', S m' => Reduce (f n' m')
      | _, _ => No
    end); congruence.
Defined.

Eval compute in eq_nat_dec 2 2.
(** %\vspace{-.15in}% [[
     = Yes
     : {2 = 2} + {2 <> 2}
     ]]
     *)

Eval compute in eq_nat_dec 2 3.
(** %\vspace{-.15in}% [[
     = No
     : {2 = 3} + {2 <> 3}
     ]]

(* Note that the %\coqdocnotation{%#<tt>#Yes#</tt>#%}% and %\coqdocnotation{%#<tt>#No#</tt>#%}% notations are hiding proofs establishing the correctness of the outputs.*)

%\coqdocnotation{%#<tt>#Yes#</tt>#%}%および%\coqdocnotation{%#<tt>#No#</tt>#%}%が、出力の正しさを確立する、隠された証明を表しています。

(* Our definition extracts to reasonable OCaml code. *)

上記の定義からは妥当なOCamlのコードが抽出できます。
*)

Extraction eq_nat_dec.

(**
<<
(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n0 -> Right)
    | S n' -> (match m with
                 | O -> Right
                 | S m' -> eq_nat_dec n' m')
>>

(* Proving this kind of decidable equality result is so common that Coq comes with a tactic for automating it.%\index{tactics!decide equality}% *)

このような等価性の決定可能性に対する証明は頻出するので、Coqには自動化のためのタクティクがあります%\index{タクティク!decide equality}%。
*)

Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.

(**
(* Curious readers can verify that the [decide equality] version extracts to the same OCaml code as our more manual version does.  That OCaml code had one undesirable property, which is that it uses <<Left>> and <<Right>> constructors instead of the Boolean values built into OCaml.  We can fix this, by using Coq's facility for mapping Coq inductive types to OCaml variant types.%\index{Vernacular commands!Extract Inductive}% *)

興味がある読者は、[decide equality]を使った上記の証明からも、手作業で書いた先の証明によるものと同じOCamlのコードが抽出されることを確かめてみましょう。
OCamlのコードには、一点、非決定的な性質があります。
それは、OCamlに埋め込まれているブール値ではなく、<<Left>>および<<Right>>という構成子が使われていることです。
Coqの帰納型をOCamlのヴァリアント型に写す機能を使えば、この非決定性を修正できます。
%\index{Vernacular commands!Extract Inductive}%
*)

Extract Inductive sumbool => "bool" ["true" "false"].
Extraction eq_nat_dec'.

(**
<<
(** val eq_nat_dec' : nat -> nat -> bool **)

let rec eq_nat_dec' n m0 =
  match n with
    | O -> (match m0 with
              | O -> true
              | S n0 -> false)
    | S n0 -> (match m0 with
                 | O -> false
                 | S n1 -> eq_nat_dec' n0 n1)
>>

(* We can build "smart" versions of the usual Boolean operators and put them to good use in certified programming.  For instance, here is a [sumbool] version of Boolean "or." *)

一般的なBooleanの演算子を使う「スマート」なバージョンを組み立てて、それを証明付きのプログラムで上手に使うことも可能です。
たとえば、[sumbool]用の「[||]」はこのように組み立てられます。
*)

(* EX: Write a function that decides if an element belongs to a list. *)

(* begin thide *)
Notation "x || y" := (if x then Yes else Reduce y).

(**
(* Let us use it for building a function that decides list membership.  We need to assume the existence of an equality decision procedure for the type of list elements. *)

この[sumbool]を使って、ある要素がリストに含まれるかどうかを決定する関数を作ってみましょう。
リストの要素の型に対して等価性を決定する[A_eq_dec]という手続きの存在を仮定します。
*)

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  (**
  (* The final function is easy to write using the techniques we have developed so far. *)
  
  作りたい関数は、ここまでの例で説明した方法で簡単に書けます。
  *)

  Definition In_dec : forall (x : A) (ls : list A), {In x ls} + {~ In x ls}.
    refine (fix f (x : A) (ls : list A) : {In x ls} + {~ In x ls} :=
      match ls with
	| nil => No
	| x' :: ls' => A_eq_dec x x' || f x ls'
      end); crush.
  Defined.
End In_dec.

Eval compute in In_dec eq_nat_dec 2 (1 :: 2 :: nil).
(** %\vspace{-.15in}% [[
     = Yes
     : {In 2 (1 :: 2 :: nil)} + { ~ In 2 (1 :: 2 :: nil)}
     ]]
     *)

Eval compute in In_dec eq_nat_dec 3 (1 :: 2 :: nil).
(** %\vspace{-.15in}% [[
     = No
     : {In 3 (1 :: 2 :: nil)} + { ~ In 3 (1 :: 2 :: nil)}
     ]]

(* The [In_dec] function has a reasonable extraction to OCaml. *)

[In_dec]関数からは妥当なOCamlのコードが抽出できます。
*)

Extraction In_dec.
(* end thide *)

(**
<<
(** val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec a_eq_dec x = function
  | Nil -> false
  | Cons (x', ls') ->
      (match a_eq_dec x x' with
         | true -> true
         | false -> in_dec a_eq_dec x ls')
>>

(* This is more or less the code for the corresponding function from the OCaml standard library. *)

このコードは、おおむねOCamlの標準ライブラリにある関数のコードに対応しています。
*)

(**

(* * Partial Subset Types *)
* 部分的な部分集合型

(* Our final implementation of dependent predecessor used a very specific argument type to ensure that execution could always complete normally.  Sometimes we want to allow execution to fail, and we want a more principled way of signaling failure than returning a default value, as [pred] does for [0].  One approach is to define this type family %\index{Gallina terms!maybe}%[maybe], which is a version of [sig] that allows obligation-free failure. *)

依存型による前者関数の最後の実装例は、「実行すれば常に正常に完了する」ことを表すとても特別な引数の型を使う方法です。
実行が失敗で完了するという状況も許容したいので、失敗を表すのにデフォルトの値（[pred]の場合に[0]）を使うのではなく、もっと規律正しい方法が必要です。
そのための手法のひとつとして、proof obligationなしに失敗を許容するような[sig]型の一種である%\index{Gallina terms!maybe}%[maybe]を使うという手があります。
*)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(**
(* We can define some new notations, analogous to those we defined for subset types. *)

部分集合型のときのように、[maybe]型についても同じような記法を定義できます。
*)

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

(**
(* Now our next version of [pred] is trivial to write. *)

上記の記法を使って[pred]を簡単に書けます。
*)

Definition pred_strong7 : forall n : nat, {{m | n = S m}}.
  refine (fun n =>
    match n return {{m | n = S m}} with
      | O => ??
      | S n' => [|n'|]
    end); trivial.
Defined.

Eval compute in pred_strong7 2.
(** [[
     = [|1|]
     : {{m | 2 = S m}}
    ]]
*)

Eval compute in pred_strong7 0.
(** [[
     = ??
     : {{m | 0 = S m}}
     ]]

(* Because we used [maybe], one valid implementation of the type we gave [pred_strong7] would return [??] in every case.  We can strengthen the type to rule out such vacuous implementations, and the type family %\index{Gallina terms!sumor}%[sumor] from the standard library provides the easiest starting point.  For type [A] and proposition [B], [A + {B}] desugars to [sumor A B], whose values are either values of [A] or proofs of [B]. *)

[pred_strong7]の型は、[maybe]を使っているので、「どのような場合についても[??]を返す」という実装でも有効になってしまいます。
もっと強い型を使うことで、そうした意味のない実装を排除できます。
手始めに、標準ライブラリの%\index{Gallina terms!sumor}%[sumor]という型族を使ってみましょう。
型[A]および命題[B]について、[A + {B}]という構文糖衣が展開されたものが[sumor A B]です。その値は、「[A]の値もしくは[B]の証明のいずれか」を表します。
*)

Print sumor.
(** %\vspace{-.15in}% [[
Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}
]]

(* We add notations for easy use of the [sumor] constructors.  The second notation is specialized to [sumor]s whose [A] parameters are instantiated with regular subset types, since this is how we will use [sumor] below. *)

[sumor]の構成子に対する便利な記法を二つ追加します。
二つめは、「[sumor]の変数のうち[A]のほうが、通常の部分集合型で具体化されているもの」に特化した記法です。
この後、[sumor]をそのように使うので、このような記法をここで用意しました。
*)

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

(**
(* Now we are ready to give the final version of possibly failing predecessor.  The [sumor]-based type that we use is maximally expressive; any implementation of the type has the same input-output behavior. *)

ここまでの準備で、「失敗するかもしれない前者関数」の最終バージョンが書けます。
下記の例の[sumor]を使った型は、とても表現力が高いものになっています。
この型に対するどのような実装も、入出力に関して同じ振る舞いを示します。
*)

Definition pred_strong8 : forall n : nat, {m : nat | n = S m} + {n = 0}.
  refine (fun n =>
    match n with
      | O => !!
      | S n' => [||n'||]
    end); trivial.
Defined.

Eval compute in pred_strong8 2.
(** [[
     = [||1||]
     : {m : nat | 2 = S m} + {2 = 0}
    ]]
*)

Eval compute in pred_strong8 0.
(** [[
     = !!
     : {m : nat | 0 = S m} + {0 = 0}
    ]]

(* As with our other maximally expressive [pred] function, we arrive at quite simple output values, thanks to notations. *)

この[pred]関数は、記法をうまく用意したおかげで、きわめて表現力が高いながら実に簡潔に値が出力されています。
*)

(**
(* * Monadic Notations *)

* モナド記法

(* We can treat [maybe] like a monad%~\cite{Monads}\index{monad}\index{failure monad}%, in the same way that the Haskell <<Maybe>> type is interpreted as a failure monad.  Our [maybe] has the wrong type to be a literal monad, but a "bind"-like notation will still be helpful.  %Note that the notation definition uses an ASCII \texttt{<-}, while later code uses (in this rendering) a nicer left arrow $\leftarrow$.% *)

[maybe]は、Haskellの<<Maybe>>が失敗を表すモナドとして解釈できるのと同じく、%~\cite{Monads}\index{モナド}\index{失敗を表すモナド}%モナドとして扱えます。
[maybe]の型は、文字通りのモナドにはなれないのですが、それでもバインドのような記法が使えると便利です。
なお、下記の記法の定義ではASCII文字による%\texttt{<-}%を使っていますが、その後のコード例では、この記法を表すのに左向き矢印（$\leftarrow$）を使います。
*)

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

(**
(* The meaning of [x <- e1; e2] is: First run [e1].  If it fails to find an answer, then announce failure for our derived computation, too.  If [e1] _does_ find an answer, pass that answer on to [e2] to find the final result.  The variable [x] can be considered bound in [e2]. *)

[x <- e1; e2]の意味は、「最初に[e1]を実行する」です。
答えを見つけるのに失敗したら、計算によって導出されたものについても、失敗であると通告します。
[e1]が確かに答えを見つけたら、その答えを[e2]に渡し、最終的な結果を探します。
[x]は、[e2]において束縛されているとみなされます。

(* This notation is very helpful for composing richly typed procedures.  For instance, here is a very simple implementation of a function to take the predecessors of two naturals at once. *)

豊かな型を持つ手続きを組み合わせるときには、このような記法がとても便利です。
以下の例は、二つの自然数の前者を一度に見つける関数の実装例です。
*)

(* EX: Write a function that tries to compute predecessors of two [nat]s at once. *)

(* begin thide *)
Definition doublePred : forall n1 n2 : nat, {{p | n1 = S (fst p) /\ n2 = S (snd p)}}.
  refine (fun n1 n2 =>
    m1 <- pred_strong7 n1;
    m2 <- pred_strong7 n2;
    [|(m1, m2)|]); tauto.
Defined.
(* end thide *)

(**
(* We can build a [sumor] version of the "bind" notation and use it to write a similarly straightforward version of this function.  %Again, the notation definition exposes the ASCII syntax with an operator \texttt{<-{}-}, while the later code uses a nicer long left arrow $\longleftarrow$.% *)

[sumor]に対しても同じような記法を定義し、それを使って上記の関数を定義することも簡単です。
（この例でも、記法の定義では演算子をASCII文字による\texttt{<--}で表しますが、その後のコード例ではこれを$\longleftarrow$で表しています。）

(** %\def\indash{-}\catcode`-=13\def-{\indash\kern0pt }% *)

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

(** %\catcode`-=12% *)(* *)
(** printing * $\times$ *)

(* EX: Write a more expressively typed version of the last exercise. *)

(* begin thide *)
Definition doublePred' : forall n1 n2 : nat,
  {p : nat * nat | n1 = S (fst p) /\ n2 = S (snd p)}
  + {n1 = 0 \/ n2 = 0}.
  refine (fun n1 n2 =>
    m1 <-- pred_strong8 n1;
    m2 <-- pred_strong8 n2;
    [||(m1, m2)||]); tauto.
Defined.
(* end thide *)

(**
(* This example demonstrates how judicious selection of notations can hide complexities in the rich types of programs. *)

この例からも、型が豊かなプログラムでは記法を上手に決めることで複雑さを隠せることがわかります。
*)

(** * A Type-Checking Example *)

(** We can apply these specification types to build a certified type checker for a simple expression language. *)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

(** We define a simple language of types and its typing rules, in the style introduced in Chapter 4. *)

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
  hasType (Nat n) TNat
| HtPlus : forall e1 e2,
  hasType e1 TNat
  -> hasType e2 TNat
  -> hasType (Plus e1 e2) TNat
| HtBool : forall b,
  hasType (Bool b) TBool
| HtAnd : forall e1 e2,
  hasType e1 TBool
  -> hasType e2 TBool
  -> hasType (And e1 e2) TBool.

(** It will be helpful to have a function for comparing two types.  We build one using [decide equality]. *)

(* begin thide *)
Definition eq_type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

(** Another notation complements the monadic notation for [maybe] that we defined earlier.  Sometimes we want to include "assertions" in our procedures.  That is, we want to run a decision procedure and fail if it fails; otherwise, we want to continue, with the proof that it produced made available to us.  This infix notation captures that idea, for a procedure that returns an arbitrary two-constructor type. *)

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

(** With that notation defined, we can implement a [typeCheck] function, whose code is only more complex than what we would write in ML because it needs to include some extra type annotations.  Every [[|e|]] expression adds a [hasType] proof obligation, and [crush] makes short work of them when we add [hasType]'s constructors as hints. *)
(* end thide *)

Definition typeCheck : forall e : exp, {{t | hasType e t}}.
(* begin thide *)
  Hint Constructors hasType.

  refine (fix F (e : exp) : {{t | hasType e t}} :=
    match e return {{t | hasType e t}} with
      | Nat _ => [|TNat|]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;;
        eq_type_dec t2 TNat;;
        [|TNat|]
      | Bool _ => [|TBool|]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [|TBool|]
    end); crush.
(* end thide *)
Defined.

(** Despite manipulating proofs, our type checker is easy to run. *)

Eval simpl in typeCheck (Nat 0).
(** %\vspace{-.15in}% [[
     = [|TNat|]
     : {{t | hasType (Nat 0) t}}
     ]]
     *)

Eval simpl in typeCheck (Plus (Nat 1) (Nat 2)).
(** %\vspace{-.15in}% [[
     = [|TNat|]
     : {{t | hasType (Plus (Nat 1) (Nat 2)) t}}
     ]]
     *)

Eval simpl in typeCheck (Plus (Nat 1) (Bool false)).
(** %\vspace{-.15in}% [[
     = ??
     : {{t | hasType (Plus (Nat 1) (Bool false)) t}}
     ]]

The type checker also extracts to some reasonable OCaml code. *)

Extraction typeCheck.

(**
<<
(** val typeCheck : exp -> type0 maybe **)

let rec typeCheck = function
  | Nat n -> Found TNat
  | Plus (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TNat with
                       | true ->
                           (match eq_type_dec t2 TNat with
                              | true -> Found TNat
                              | false -> Unknown)
                       | false -> Unknown)))
  | Bool b -> Found TBool
  | And (e1, e2) ->
      (match typeCheck e1 with
         | Unknown -> Unknown
         | Found t1 ->
             (match typeCheck e2 with
                | Unknown -> Unknown
                | Found t2 ->
                    (match eq_type_dec t1 TBool with
                       | true ->
                           (match eq_type_dec t2 TBool with
                              | true -> Found TBool
                              | false -> Unknown)
                       | false -> Unknown)))
>>
*)

(** %\smallskip%

We can adapt this implementation to use [sumor], so that we know our type-checker only fails on ill-typed inputs.  First, we define an analogue to the "assertion" notation. *)

(* begin thide *)
Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60).

(** Next, we prove a helpful lemma, which states that a given expression can have at most one type. *)

Lemma hasType_det : forall e t1,
  hasType e t1
  -> forall t2, hasType e t2
    -> t1 = t2.
  induction 1; inversion 1; crush.
Qed.

(** Now we can define the type-checker.  Its type expresses that it only fails on untypable expressions. *)

(* end thide *)
Definition typeCheck' : forall e : exp, {t : type | hasType e t} + {forall t, ~ hasType e t}.
(* begin thide *)
  Hint Constructors hasType.

  (** We register all of the typing rules as hints. *)

  Hint Resolve hasType_det.

  (** The lemma [hasType_det] will also be useful for proving proof obligations with contradictory contexts.  Since its statement includes [forall]-bound variables that do not appear in its conclusion, only [eauto] will apply this hint. *)

  (** Finally, the implementation of [typeCheck] can be transcribed literally, simply switching notations as needed. *)

  refine (fix F (e : exp) : {t : type | hasType e t} + {forall t, ~ hasType e t} :=
    match e return {t : type | hasType e t} + {forall t, ~ hasType e t} with
      | Nat _ => [||TNat||]
      | Plus e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TNat;;;
        eq_type_dec t2 TNat;;;
        [||TNat||]
      | Bool _ => [||TBool||]
      | And e1 e2 =>
        t1 <-- F e1;
        t2 <-- F e2;
        eq_type_dec t1 TBool;;;
        eq_type_dec t2 TBool;;;
        [||TBool||]
    end); clear F; crush' tt hasType; eauto.

  (** We clear [F], the local name for the recursive function, to avoid strange proofs that refer to recursive calls that we never make.  Such a step is usually warranted when defining a recursive function with [refine].  The [crush] variant %\index{tactics!crush'}%[crush'] helps us by performing automatic inversion on instances of the predicates specified in its second argument.  Once we throw in [eauto] to apply [hasType_det] for us, we have discharged all the subgoals. *)
(* end thide *)


Defined.

(** The short implementation here hides just how time-saving automation is.  Every use of one of the notations adds a proof obligation, giving us 12 in total.  Most of these obligations require multiple inversions and either uses of [hasType_det] or applications of [hasType] rules.

   Our new function remains easy to test: *)

Eval simpl in typeCheck' (Nat 0).
(** %\vspace{-.15in}% [[
     = [||TNat||]
     : {t : type | hasType (Nat 0) t} +
       {(forall t : type, ~ hasType (Nat 0) t)}
       ]]
       *)

Eval simpl in typeCheck' (Plus (Nat 1) (Nat 2)).
(** %\vspace{-.15in}% [[
     = [||TNat||]
     : {t : type | hasType (Plus (Nat 1) (Nat 2)) t} +
       {(forall t : type, ~ hasType (Plus (Nat 1) (Nat 2)) t)}
       ]]
       *)

Eval simpl in typeCheck' (Plus (Nat 1) (Bool false)).
(** %\vspace{-.15in}% [[
     = !!
     : {t : type | hasType (Plus (Nat 1) (Bool false)) t} +
       {(forall t : type, ~ hasType (Plus (Nat 1) (Bool false)) t)}
       ]]

The results of simplifying calls to [typeCheck'] look deceptively similar to the results for [typeCheck], but now the types of the results provide more information. *)
