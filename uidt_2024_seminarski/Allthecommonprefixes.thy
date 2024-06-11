theory Allthecommonprefixes
  imports Main "HOL-Data_Structures.Queue_2Lists" 
begin






(* 15.1 i uvodna teorema *)

fun llcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "llcp xs [] = 0"
| "llcp [] ys = 0"
| "llcp (x # xs) (y # ys) = (if x = y then 1 + llcp xs ys else 0)"



value "llcp [1::nat, 2, 3, 4] [1, 2, 4, 2]"
value "llcp [1::nat, 2, 3, 4] [2, 2, 3, 5]"
value "llcp [5::nat, 5, 5, 5] [5, 5, 5, 5,5]"



(*NAIVNI ALGORITAM*)

fun tails :: "'a list \<Rightarrow> 'a list list" where
  "tails [] = []" |
  "tails xs = xs # tails (tl xs)"

definition allcp'' :: "nat list \<Rightarrow> nat list" where
  "allcp'' xs = map (llcp xs) (tails xs)"

value "allcp'' [2,2,2,4]"


(*uvodna teorema*)

lemma llcp_drop:
  assumes "llcp us vs = m"
  shows "llcp (drop m us) (drop m vs) = llcp us vs - m"
proof -
  from assms show ?thesis
    by (induction m arbitrary: us vs) simp
qed


theorem llcp_theorem:
  assumes "llcp us vs = m" and "llcp vs ws = n"
  shows "llcp us ws = (if m \<noteq> n then min m n else m + llcp (drop m us) (drop m ws))"
proof (cases "m = n")
  case True
  then have "llcp us ws = m + llcp (drop m us) (drop m ws)"
  proof -
    from True have m_eq: "m = n" by simp
    from assms have "llcp us vs = m" "llcp vs ws = m" using m_eq by auto
    show ?thesis
      by simp
  qed
  with True show ?thesis by simp
next
  case False
  then show ?thesis
  proof -
    from False have "m \<noteq> n" by simp
    then show ?thesis
      using assms
      by (metis llcp.simps list.sel(3) min_def llcp_drop)
  qed
qed



fun fst4 :: "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> 'a" where
  "fst4 (a, b, c, d) = a"

value "fst4 (1::nat, 2::nat, 3::nat, 4::nat)"            
value "fst4 (True, False, True, False)" 
value "fst4 ((1::nat, 2::nat), (3::nat, 4::nat), (5::nat, 6::nat), (7::nat, 8::nat))" 



fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc xs x = xs @ [x]"

value "snoc [1::nat, 2, 3] 4"  (* Očekivani rezultat: [1, 2, 3, 4] *)
value "snoc [] (1::nat)"  (* Očekivani rezultat: [1] *)

fun done_f :: "nat \<Rightarrow> (nat list * nat * nat * nat) \<Rightarrow> bool" where
  "done_f n (as, i, p, k) = (k = n)"

value "done_f 5 ([0, 1, 2, 3, 4], 0, 0, 5)"  (* Očekivani rezultat: True *)
value "done_f 5 ([0, 1, 2, 3, 4], 0, 0, 4)"  (* Očekivani rezultat: False *)

fun step :: "'a list \<Rightarrow> (nat list * nat * nat * nat) \<Rightarrow> (nat list * nat * nat * nat)" where
  "step xs (as, i, p, k) = 
    (let q = as ! (k - i);
         r = p - (k - i);
         a = llcp xs (drop k xs);
         b = q + llcp (drop q xs) (drop (q + k) xs)
     in if k \<ge> i + p then (snoc as a, k, a, k + 1)
        else if q \<noteq> r then (snoc as (min q r), i, p, k + 1)
        else (snoc as b, k, b, k + 1))"

definition test_xs :: "nat list" where
  "test_xs = [1, 2, 3, 2, 1]"

value "step test_xs ([0, 1, 2], 1, 2, 3)"  (* Primer rezultata *)

partial_function (tailrec) until_f :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "until_f P f x = (if P x then x else until_f P f (f x))"

declare until_f.simps [code]


(*15.1*)
definition allcp :: "'a list \<Rightarrow> nat list" where
"allcp xs = (
     let n = length xs
     in fst4 (until_f (done_f n) (step xs) ([n], 0, 0, 1)))"


definition test_xs' :: "nat list" where
  "test_xs' = [1, 2, 3, 2, 1]"



export_code llcp fst4 snoc done_f step until_f allcp in Haskell

(*nakon pokretanja koda u Haskellu dobio sam ispravne rezultate za sve test primere*)





(* 15.2 *)

type_synonym 'a array = "nat \<rightharpoonup> 'a"
(*niz preko mape*)



 (* usled nemogucnosti implementacije niza pomocu strukture Array,
 a ogranicenosti pristupa elementima u okviru reda,
 ovde smo primorani da koristimo listu sto nam automatski rusi slozenost *)

(* Definisanje funkcije llcp' sa terminacionim dokazom *)
function llcp' :: "nat queue \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "llcp' xa n j k= (if j = n \<or> k = n  then 0
                else if ((list xa)!j) \<noteq> ((list xa)! k) then 0
                else 1 + llcp' xa n (j + 1) (k + 1))"
  by pat_completeness auto



(* Funkcija step iz segmenta 15.2 *)
fun step'  :: "nat queue \<times> nat queue \<times> nat \<times> nat \<Rightarrow> nat queue \<times> nat queue \<times> nat \<times> nat" where
  "step' (as, qs, h, k) = 
    (let q = first qs;
         qs' = deq qs;
         r = h - k;
         n = length (list as);
         a = llcp' as n 0 k;
         as' = deq as;
         b = llcp' as n  q (q + k)
     in if k \<ge> h then
          (enq a as, enq a as', k+a, k + 1)
        else if q \<noteq> r then
          (enq (min q r) as,enq (min q r) qs', h, k + 1)
        else
          (enq b as, enq b as', k+b, k + 1))"

 (* usled nemogucnosti implementacije niza pomocu strukture Array,
 a ogranicenosti pristupa elementima u okviru reda,
 ovde smo primorani da koristimo listu sto nam automatski rusi slozenost *)

(* Funkcija extract iz segmenta 15.2 *)
fun extract' :: "nat queue \<times> nat queue \<times> nat \<times> nat \<Rightarrow> nat list" where
  "extract' (as, qs, h, k) = list as"

fun done' :: "nat queue \<times> nat queue \<times> nat \<times> nat \<Rightarrow> bool" where
  "done' (as, qs, h, k) = (k = length(list as))"



partial_function (tailrec) until :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "until P f x = (if P x then x else until P f (f x))"


declare until.simps [code]


(*po definiciji praznog reda u dokumentaciji mozemo videti da se empty pise kao ([],[])
  jer je red predstavljen kao nat list x nat list...
*)

(* Glavna funkcija allcp iz segmenta 15.2 *)
definition  allcp' :: "nat list \<Rightarrow> nat list" where
  "allcp' xs = extract'(until done' step' ((xs,[]), ([],[]), 0, 1))"



(*nakon pokretanja koda u Haskellu dobio sam ispravne rezultate za sve test primere*)


end
