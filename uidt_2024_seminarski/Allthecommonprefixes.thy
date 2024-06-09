theory Allthecommonprefixes
  imports Main
begin


(* 15.1 i uvodna teorema *)

fun llcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "llcp xs [] = 0"
| "llcp [] ys = 0"
| "llcp (x # xs) (y # ys) = (if x = y then 1 + llcp xs ys else 0)"


value "llcp [1::nat, 2, 3, 4] [1, 2, 4, 2]"
value "llcp [1::nat, 2, 3, 4] [2, 2, 3, 5]"
value "llcp [5::nat, 5, 5, 5] [5, 5, 5, 5,5]"


(*uvodna teorema*)
lemma llcp_theorem:
  assumes "llcp us vs = m"
    and "llcp vs ws = n"
  shows "llcp us ws = (if m \<noteq> n then min m n else m + llcp (drop m us) (drop m ws))"
proof (cases "m = n")
  case True
  then show ?thesis
    using assms
  proof (induct m arbitrary: us vs ws)
    case 0
    then show ?case
      by auto
  next
    case (Suc m)
    then obtain x xs y ys z zs where "us = x # xs" and "vs = y # ys" and "ws = z # zs"
      using llcp.elims by blast
    then show ?case
    proof (cases "x = y \<and> y = z")
      case True
      then have "llcp (x # xs) (y # ys) = Suc m" and "llcp (y # ys) (z # zs) = Suc n"
        using Suc by auto
      then show ?thesis
        using Suc.IH[of xs ys zs] True by auto
    next
      case False
      then show ?thesis
        using Suc.prems llcp.simps(3) by auto
    qed
  qed
next
  case False
  then show ?thesis
  proof (cases "m < n")
    case True
    then have "llcp us vs = m" and "llcp vs ws = n" and "llcp us ws = m"
      using assms by auto
    then show ?thesis
      using False True by auto
  next
    case False
    then have "llcp us vs = m" and "llcp vs ws = n" and "llcp us ws = n"
      using assms by auto
    then show ?thesis
      using False True by auto
  qed
qed


fun fst4 :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a" where
  "fst4 (a, b, c, d) = a"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc xs x = xs @ [x]"

fun done_f :: "nat \<Rightarrow> (nat list * nat * nat * nat) \<Rightarrow> bool" where
  "done_f n (as, i, p, k) = (k = n)"

fun step :: "'a list \<Rightarrow> (nat list * nat * nat * nat) \<Rightarrow> (nat list * nat * nat * nat)" where
  "step xs (as, i, p, k) = 
    (let q = as ! (k - i);
         r = p - (k - i);
         a = llcp xs (drop k xs);
         b = q + llcp (drop q xs) (drop (q + k) xs)
     in if k \<ge> i + p then (snoc as a, k, a, k + 1)
        else if q \<noteq> r then (snoc as (min q r), i, p, k + 1)
        else (snoc as b, k, b, k + 1))"



function until_f :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "until_f P f x = (if P x then x else until_f P f (f x))"
  by pat_completeness auto

function  allcp :: "'a list \<Rightarrow> nat list" where
"allcp xs = (
     let n = length xs
     in fst4 (until_f (done_f n) (step xs) ([n], 0, 0, 1)))"
  by auto







(* 15.2 *)


consts n :: nat
consts xa :: "nat list"

(* Pomocne funkcije iz segmenta 15.1 koje su potrebne za 15.2 *)

fun elems :: "nat list \<Rightarrow> nat list" where
  "elems as = as"

fun insert :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "insert as a = a # as"

fun remove :: "nat list \<Rightarrow> nat list \<times> nat" where
  "remove (x#xs) = (xs, x)"
| "remove [] = ([], 0)" (* Dodavanje obrasca za praznu listu *)

fun snd :: "nat list \<times> nat \<Rightarrow> nat" where
  "snd (xs, x) = x"

(* Definisanje funkcije llcp' sa terminacionim dokazom *)
function llcp' :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "llcp' j k = (if j = n \<or> k = 0 then 0
                else if (xa ! j) \<noteq> (xa ! k) then 0
                else 1 + llcp' (j + 1) (k + 1))"
  by pat_completeness auto

(* Funkcija step iz segmenta 15.2 *)
fun step'  :: "nat list \<times> nat list \<times> nat \<times> nat \<Rightarrow> nat list \<times> nat list \<times> nat \<times> nat" where
  "step' (as, qs, h, k) = 
    (let (qs', r) = remove qs;
         q = r;
         a = llcp' 0 k;
         b = llcp' q (q + k)
     in if k \<ge> h then
          (insert (insert as b) a, qs', h, k + 1)
        else if q \<noteq> r then
          (insert as (min q r), qs', h, k + 1)
        else
          (insert (insert as b) a, qs', h, k + 1))"

(* Funkcija extract iz segmenta 15.2 *)
fun extract' :: "nat list \<times> nat list \<times> nat \<times> nat \<Rightarrow> nat list" where
  "extract' (as, qs, h, k) = elems as"

fun done' :: "nat list \<times> nat list \<times> nat \<times> nat \<Rightarrow> bool" where
  "done' (as, qs, h, k) = (k = n)"

function until :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "until P f x = (if P x then x else until P f (f x))"
  by pat_completeness auto

(* Glavna funkcija allcp iz segmenta 15.2 *)
fun allcp' :: "nat list \<Rightarrow> nat list" where
  "allcp' xs = extract'(until done' step' (xs, [], 0, 1))"


end
