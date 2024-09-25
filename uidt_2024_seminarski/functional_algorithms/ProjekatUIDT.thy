theory ProjekatUIDT

imports Main

begin

value "[1::nat, 2, 3, 4, 5] ! 2" 

(* Definisanje funkcije union koja spaja dve sortirane liste
 i zadrzava sortiranost *)
fun union :: "('a::ord list) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "union [] ys = ys"
| "union xs [] = xs"
| "union (x#xs) (y#ys) = (if x < y then x # union xs (y#ys) else y # union (x#xs) ys)"

value " union [2::nat, 4, 6, 11] [1, 3, 5, 10]"

(* Funkcija koja računa k-ti najmanji element unije dve liste *)
fun smallest :: "nat \<Rightarrow> ('a::ord list \<times> 'a list) \<Rightarrow> 'a" where
  "smallest k (xs, ys) =  (union xs ys) ! k"

(* Lemma za indeksiranje spojene liste *)
lemma index_concat: 
  shows"(xs @ ys)! k = (if k < length xs then xs ! k else ys ! (k - length xs))"
  proof (induction xs arbitrary: k)
    case Nil
    then show ?case
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc n)
      then show ?thesis by simp
    qed
  next
    case (Cons x xs)
    then show ?case
    proof (cases k)
      case 0
      then show ?thesis by simp
    next
      case (Suc n)
      then have "(x # xs @ ys) ! Suc n = (xs @ ys) ! n" by simp
      then have "(xs @ ys) ! n = (if n < length xs then xs ! n else ys ! (n - length xs))" using Suc
      proof (cases "n < length xs")
        case True
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry 
      qed
    qed
  qed 
end
