theory surpassingProblem
  imports Main
begin

(*autorka: Isidora Majkic*)

definition primer :: "nat list" where
  "primer = [3, 2, 5, 2, 6, 1, 7, 4, 5, 3::nat]"

(*scount funkcija broji koliko ima vecih brojeva od x u listi xs*)
fun scount :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> nat" where
  "scount x xs = length (filter (\<lambda>y. x < y) xs)"
value "scount 5 primer" (*samo 6 i 7 su veci od 5*)

(* tails odredjuje za svaki element listu sufiks *)
primrec tails :: "'a list \<Rightarrow> 'a list list" where
  "tails [] = []"
| "tails (x # xs) = (x # xs) # tails xs"
value "tails primer" (*liste svih trenutnih sufiksa*)

(* list_max odredjuje najveci element u listi *)
primrec list_max :: "nat list \<Rightarrow> nat" where
  "list_max [] = 0" |
  "list_max (x # xs) = max x (list_max xs)"
value "list_max primer"

(* glavna funkcija, prva verzija *)
primrec msc_first :: "'a::ord list \<Rightarrow> nat" where
  "msc_first [] = 0"
| "msc_first (x # xs) = list_max (map (\<lambda>suf. scount (hd suf) (tl suf)) (tails (x # xs)))"
value "msc_first primer"

(* prvo pomocno tvrdjenje
tails (xs ++ ys) = map (++ys) (tails xs) ++ tails ys*)
lemma tails_concat: "tails (xs @ ys) = map (\<lambda> suf. suf @ ys) (tails xs) @ tails ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

(*table xs = [(z , scount z zs) | z : zs \<leftarrow> tails xs]*)
fun table:: "'a::ord  list \<Rightarrow> ('a \<times> nat) list" where
  "table [] = []"
| "table (x # xs) = (x, scount x xs) # (table xs)"
value "length (table primer)"
value "length primer"

(*msc = maximum \<sqdot> map snd \<sqdot> table*)
primrec msc_table :: "'a::linorder list \<Rightarrow> nat" where
  "msc_table [] = 0"
| "msc_table (x # xs) = list_max (map snd (table (x # xs) ) )"
value "msc_table primer"


(*tcount je pomocna fja koja racuna koliko je elemenata u tabeli vece od datog elementa.
to se koristi posle za join
tcount z tys = scount z (map fst tys)*)
fun tcount:: "'a::ord \<Rightarrow> ('a \<times> nat) list \<Rightarrow> nat" where
"tcount z tys = scount z (map fst tys)"
value "tcount 4 (table primer)" (*5, 6, 7, 5*)

(*join txs tys = [(z , c + tcount z tys) | (z , c) \<leftarrow> txs] ++ tys*)
fun join :: "('a::ord \<times> nat) list \<Rightarrow> ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "join [] tys = tys"
| "join ((x, c) # txs) tys = (x, c + tcount x tys) # join txs tys"
value "join (table primer) [(3,1)]" (*nisam sigurna da ovo treba tako da radi*)

(*ovo mi se pojavilo kao neophodno pomocno tvrdjenje za dokaz ispod,
a deluje mi tacno*)
lemma pom[simp]:
  "length (filter ((<) x) ys) = length (filter ((<) x \<circ> fst) (table ys))"
proof (induction ys)
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  then show ?case by auto
qed

(* tvrdjenje broj 2
table (xs ++ ys) = join (table xs) (table ys)*)
lemma table_append:
  "table (xs @ ys) = join (table xs) (table ys)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have "table ((x # xs) @ ys) = (x, scount x (xs @ ys)) # table (xs @ ys)"
    by auto
  also have "... = (x, scount x xs + scount x ys) # join (table xs) (table ys)"
    using Cons by auto
  also have "... = join ((x, scount x xs) # table xs) (table ys)"
    by auto
  also have "... = join (table (x # xs)) (table ys)"
    by auto
  finally show ?case .
qed

(*ovo je jeftiniji nacin racunanja fje tcount*)
fun tcount_opt:: "'a::ord \<Rightarrow> ('a \<times> nat) list \<Rightarrow> nat" where
"tcount_opt z tys = length (dropWhile (\<lambda> (y, c). z \<ge> y) tys)"

(*ovaj dokaz postoji u knjizi*)
lemma tcount_opt:
  assumes "sorted (map fst tys)" (*ako je tabela sortirana po prvom elementu*)
  shows "tcount z tys = tcount_opt z tys"
proof -
  have "tcount z tys = scount z (map fst tys)"
    by auto
  also have "... = length (filter (\<lambda>y. z < y) (map fst tys))"
    by auto
  also have "...  = length (map fst (filter ((\<lambda>y. z < y)\<circ>fst) tys) )"
    by auto
  also have "...  = length (filter ((\<lambda>y. z < y)\<circ>fst) tys)"
    by auto
  also have "... = length (dropWhile ((\<lambda>y. z \<ge> y)\<circ>fst) tys)"
    using assms
    sorry
  also have "... = length (dropWhile (\<lambda> (y, c). z \<ge> y) tys)"
    sorry
  finally show ?thesis
    by auto
qed

(*deljenje liste*)
value "primer"
value "take ((length primer) div 2) primer"
value "drop ((length primer) div 2) primer"

(*table (xs ++ ys) = join (table xs) (table ys)*)
fun table_join :: "'a::ord list  \<Rightarrow> ('a \<times> nat) list" where
  "table_join xs = join (table (take ((length xs) div 2) xs)) (table (drop ((length xs) div 2) xs))"

value "table primer"
value "table_join primer"

(*koriscenje optimizovane opcije za table*)
primrec msc_table_opt :: "'a::linorder list \<Rightarrow> nat" where
  "msc_table_opt [] = 0"
| "msc_table_opt (x # xs) = list_max (map snd (table_join (x # xs) ) )"
value "msc_table_opt primer"

(* sortirana tabela *)
fun table_sorted:: "'a::linorder  list \<Rightarrow> ('a \<times> nat) list" where
  "table_sorted xs = sort_key fst (table xs)"
value "table_sorted primer"

(* funkcija za spajanje dve sortirane tabele
join_merge txs tys = [(x , c + tcount x tys) | (x , c) \<leftarrow> txs] \<and>\<and> tys *)
fun join_merge :: "('a::ord \<times> nat) list \<Rightarrow> ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "join_merge [] tys = tys" |
  "join_merge txs [] = txs" |
  "join_merge ((x, n1) # txs) ((y, n2) # tys) =
     (if x < y then (x, n1  + length ((y, n2) # tys)) # join_merge txs ((y, n2) # tys)
      else (if x = y then (x, n1) # join_merge txs tys
            else (y, n2) # join_merge ((x, n1) # txs) tys))"

(*novi join, sortirana tabela*)
fun table_join_merge :: "'a::linorder list  \<Rightarrow> ('a \<times> nat) list" where
  "table_join_merge xs = join_merge (table_sorted (take ((length xs) div 2) xs)) (table_sorted (drop ((length xs) div 2) xs))"

(*sve poslednje verzije fja*)
primrec msc_table_last :: "'a::linorder list \<Rightarrow> nat" where
  "msc_table_last [] = 0"
| "msc_table_last (x # xs) = list_max (map snd (table_join_merge (x # xs) ) )"
value "msc_table_last primer"

end
