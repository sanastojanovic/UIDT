
theory "CountdownProblem"
  imports Main
 (*autor: Pavle Velickovic 67/2017*)

begin

fun subseqs :: "nat list \<Rightarrow> nat list list" where
  "subseqs [] = [[]]"
| "subseqs (x # xs) = (subseqs xs) @ (map ((#) x) (subseqs xs))"

value "subseqs [1,2,3,4,5,6]"

datatype Op = Add | Sub | Mul | Div
datatype Expr = Num nat | App Op Expr Expr
(*type_synonym Val = nat*)

fun value_f :: "Expr \<Rightarrow> nat" where
  "value_f (Num x) = x"
| "value_f (App Add e1 e2) = (value_f e1) + (value_f e2)"
| "value_f (App Sub e1 e2) = (value_f e1) - (value_f e2)"
| "value_f (App Mul e1 e2) = (value_f e1) * (value_f e2)"
| "value_f (App Div e1 e2) = (value_f e1) div (value_f e2)"

value "value_f (Num 60)"
value "value_f (App Add (Num 40) (Num 80))"
value "value_f (App Sub (Num 220) (Num 130))"
value "value_f (App Mul (Num 15) (Num 3))"
value "value_f (App Div (Num 810) (Num 9))"

value "value_f (App Mul (App Add (Num 2) (Num 6)) (App Div (Num 40) (App Sub (Num 10) (Num 5))))"
(*
(2+6) * (40 / (10-5)) = 8 * (40 / 5) = 8 * 8 = 64
*)

fun legal1 :: "Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "legal1 Add a b = True"
| "legal1 Sub a b = (a > b)" 
| "legal1 Mul a b = True"
| "legal1 Div a b = (a mod b = 0)"

value "legal1 Add 1 2"

value "legal1 Sub 5 2"
value "legal1 Sub 2 5"

value "legal1 Mul 4 3"

value "legal1 Div 20 4"
value "legal1 Div 20 3"

fun legal2 :: "Op \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "legal2 Add a b = (a \<le> b)"
| "legal2 Sub a b = (a > b)" 
| "legal2 Mul a b = (1 < a \<and> a < b)"
| "legal2 Div a b = (1 < b \<and> a mod b = 0)"

value "legal2 Add 4 2"
value "legal2 Add 2 4"

value "legal2 Mul 4 5"
value "legal2 Mul 5 4"
value "legal2 Mul 1 4"

value "legal2 Div 20 4"
value "legal2 Div 20 1"

fun non :: "Op \<Rightarrow> Expr \<Rightarrow> bool" where
  "non op (Num x) = True"
| "non op1 (App op2 e1 e2) = (op1 \<noteq> op2)"

value "non Add (Num 9)"
value "non Sub (App Mul (Num 20) (Num 21))"
value "non Add (App Add (Num 12) (Num 10))"

fun legal3 :: "Op \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> bool" where
  "legal3 Add (e1, v1) (e2, v2) = ((v1 \<le> v2) \<and> non Sub e1 \<and> non Add e2 \<and> non Sub e2)"
| "legal3 Sub (e1, v1) (e2, v2) = ((v2 < v1) \<and> non Sub e1 \<and> non Sub e2)"
| "legal3 Mul (e1, v1) (e2, v2) = ((1 < v1 \<and> v1 \<le> v2) \<and> non Div e1 \<and> non Mul e2 \<and> non Div e2)"
| "legal3 Div (e1, v1) (e2, v2) = ((1 < v2 \<and> v1 mod v2 = 0) \<and> non Div e1 \<and> non Div e2)"

fun add :: "nat \<Rightarrow> ((nat list) \<times> (nat list)) \<Rightarrow> ((nat list) \<times> (nat list)) list" where
  "add x (ys, zs) = [(x # ys, zs), (ys, x # zs)]"

value "add 1 ([2,3], [4,5])"

(* NEOPTIMIZOVANO
fun unmerges :: "nat list \<Rightarrow> ((nat list) \<times> (nat list)) list" where (*pretpostavka je da je lista sortirana rastuce*)
  "unmerges [] = []"
| "unmerges [x,y] = [([x],[y]),([y],[x])]"
| "unmerges (x # xs) = [([x],xs),(xs,[x])] @ concat(map (add x) (unmerges xs))"
*)

fun unmerges :: "nat list \<Rightarrow> ((nat list) \<times> (nat list)) list" where (*pretpostavka je da je lista sortirana rastuce*)
  "unmerges [] = []"
| "unmerges [x,y] = [([x],[y])]"
| "unmerges (x # xs) = [([x],xs)] @ concat(map (add x) (unmerges xs))"

value "unmerges [1,2,3]"
value "unmerges [1,2,3,4]"
value "unmerges [1,2,3,4,5,6]"

(*NEOPTIMIZOVANO
fun combine :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "combine (e1,v1) (e2,v2) = [((App op e1 e2), (value_f (App op e1 e2))). op \<leftarrow> [Add, Sub, Mul, Div], legal1 op v1 v2]"
*)

(*
fun combine :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "combine (e1,v1) (e2,v2) = [((App op e1 e2), (value_f (App op e1 e2))). op \<leftarrow> [Add, Sub, Mul, Div], legal2 op v1 v2]
                            @[((App op e2 e1), (value_f (App op e2 e1))). op \<leftarrow> [Add, Sub, Mul, Div], legal2 op v2 v1]"
*)

(* bez non
fun comb1 :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "comb1 (e1,v1) (e2,v2) = [(App Add e1 e2, v1+v2), (App Sub e2 e1, v2-v1)]
                          @ (if 1 < v1 then [(App Mul e1 e2, v1*v2)]@[(App Div e2 e1, v2 div v1). v2 mod v1 = 0] else [])"

fun comb2 :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "comb2 (e1,v1) (e2,v2) = [(App Add e1 e2, v1+v2)] 
                          @ (if 1 < v1 then [(App Mul e1 e2, v1*v2), (App Div e1 e2, 1)] else [])"
*)

fun comb1 :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "comb1 (e1,v1) (e2,v2) = (if (non Sub e1 \<and> non Sub e2) then
                          ([(App Add e1 e2, v1 + v2). non Add e2] @ [(App Sub e2 e1, v2 - v1)])
                          else []) @
                          (if (1 < v1 \<and> non Div e1 \<and> non Div e2) then
                          ([(App Mul e1 e2, v1 * v2). non Mul e2] @ [(App Div e2 e1, v2 div v1). v2 mod v1 = 0])
                          else [])"

fun comb2 :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "comb2 (e1,v1) (e2,v2) = [(App Add e1 e2, v1 + v2). non Sub e1, non Add e2, non Sub e2]
                            @ (if (1 < v1 \<and> non Div e1 \<and> non Div e2) then
                            ([(App Mul e1 e2, v1 * v2). non Mul e2] @ [(App Div e1 e2, 1)])
                            else [])"

fun combine :: "(Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list" where
  "combine (e1,v1) (e2,v2) = (if v1 < v2 then (comb1 (e1,v1) (e2,v2) ) 
                              else (if v1 > v2 then comb1 (e2,v2) (e1,v1) else comb2 (e1,v1) (e2,v2)))"

value "combine (Num 10, 10) (Num 2, 2)"
value "combine (Num 10, 10) (Num 3, 3)"
value "combine (Num 10, 10) (Num 14, 14)"
value "combine (Num 9, 9) (Num 9, 9)"

(* Memoisation*)

(*Trie*)

(*Memo*)

(*empty*)

(*follow*)

(*fetch*)

(*store*)

(*mkExprs_memo*)

(*insert*)

(*memoise*)

(*extract*)

function mkExprs :: "nat list \<Rightarrow> (Expr \<times> nat) list" where
  "mkExprs [] = []"
| "mkExprs xs = [ev. (ys, zs) \<leftarrow> unmerges xs, ev1 \<leftarrow> mkExprs ys, ev2 \<leftarrow> mkExprs zs, ev \<leftarrow> combine ev1 ev2]"
  by auto

fun absdiff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "absdiff x y = (if x \<ge> y then x-y else y-x)"

fun search :: "nat \<Rightarrow> nat \<Rightarrow> (Expr \<times> nat) \<Rightarrow> (Expr \<times> nat) list \<Rightarrow> (Expr \<times> nat)" where
  "search n d ev [] = ev"
| "search n d ev ((e,v) # evs) = (if n = v then (e,v) else 
                                  (if (absdiff n v) < d then search n (absdiff n v) (e,v) evs 
                                                        else search n d ev evs))"

fun nearest :: "nat \<Rightarrow> (Expr \<times> nat) list \<Rightarrow> (Expr \<times> nat)" where
  "nearest n [] = undefined"
| "nearest n ((e,v) # evs) = (if n = v then (e,v) else search n (absdiff n v) (e,v) evs)"

value "nearest 500 [(Num 600, 600), (Num 200, 200), (Num 380, 380), (Num 499, 499)]"

(* ista definicija kao countdown3
fun countdown1 :: "nat \<Rightarrow> nat list \<Rightarrow> (Expr \<times> nat)" where
  "countdown1 n xs = nearest n (concat (map mkExprs (subseqs xs)))"

fun countdown2 :: "nat \<Rightarrow> nat list \<Rightarrow> (Expr \<times> nat)" where
  "countdown2 n xs = nearest n (concat (map mkExprs (subseqs xs)))"
*)

fun countdown3 :: "nat \<Rightarrow> nat list \<Rightarrow> (Expr \<times> nat)" where
  "countdown3 n xs = nearest n (concat (map mkExprs (subseqs xs)))"

(*
fun countdown4 :: "nat \<Rightarrow> nat list \<Rightarrow> (Expr \<times> nat)" where
  "countdown4 n xs = nearest n (extract (memoise (subseqs xs)))"
*)

(*tree*)

(*memo_tree*)

(*mkTrees*)

(*toExprs*)

(*insert_tree*)

(*memoise_tree*)

(*extract_tree*)

(*
fun countdown5 :: "nat \<Rightarrow> nat list \<Rightarrow> (Expr \<times> nat)" where
  "countdown5 n xs = nearest n (concat (map (toExprs) (extract (memoise (subseqs xs)))))" 
*)

end