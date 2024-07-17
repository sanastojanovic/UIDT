theory "06_MakingCentury"
  imports Main "HOL-Data_Structures.Array_Braun"

begin

(* Author: Andrija Urosevic *)

section \<open>Auxiliaries\<close>

primrec foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
  "foldr f acc [] = acc"
| "foldr f acc (x # xs) = f x (foldr f acc xs)"

fun sum :: "int list \<Rightarrow> int" where
  "sum xs = foldr (+) 0 xs"

fun prod :: "int list \<Rightarrow> int" where
  "prod xs = foldr (*) 1 xs"

fun concat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "concat_map f xs = foldr ((@) \<circ> f) [] xs"

lemma fusion_foldr:
  assumes "f a = b"
      and "\<And> x y. f (g x y) = h x (f y)"
    shows "(f \<circ> foldr g a) = (foldr h b)"
proof
  fix xs
  show "(f \<circ> foldr g a) xs = (foldr h b) xs"
    by (induction xs) (simp add: assms(1), simp add: assms(2))
qed

fun fork :: "('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c"  where 
  "fork (f , g) x = (f x , g x)"

fun cross :: "('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'b \<times> 'd" where
  "cross (f , g) (x , y) = (f x , g y)"

lemma fst_fork: "fst \<circ> fork (f , g) = f"
  by auto

lemma snd_fork: "snd \<circ> fork (f , g) = g"
  by auto

lemma fusion_fork: "fork (f , g) \<circ> h = fork (f \<circ> h , g \<circ> h)"
  by auto

lemma cross_fork: "fork (f \<circ> h , g \<circ> k) = cross (f , g) \<circ> fork (h, k)"
  by auto

fun zip :: "'a list \<times> 'b list \<Rightarrow> ('a \<times> 'b) list" where
  "zip (xs, ys) = List.zip xs ys"

fun unzip :: "('a \<times> 'b) list \<Rightarrow> 'a list \<times> 'b list" where
  "unzip xs = fork (map fst, map snd) xs"

lemma map_composition: "map (f \<circ> g) = map f \<circ> map g"
  by auto

lemma fork_map_unzip: "fork (map f , map g) = unzip \<circ> map (fork (f , g))"
proof -
  have "unzip \<circ> map (fork (f , g)) = fork (map fst, map snd ) \<circ> map (fork (f , g))"
    by auto
  also have "... = fork (map (fst \<circ> fork (f , g)), map (snd \<circ> fork (f , g)))"
    using fusion_fork map_composition
    by auto
  also have "... = fork (map f , map g)"
    using fst_fork[of f g] snd_fork[of f g]
    by simp
  finally show ?thesis
    by simp
qed

lemma zip_unzip_id: "(zip \<circ> unzip) = id"
proof
  fix xs
  show "(zip \<circ> unzip) xs = id xs"
    by (induction xs) auto
qed

lemma map_fork_zip: "map (fork (f , g)) = zip \<circ> fork (map f , map g)"
proof -
  have "(unzip \<circ> map (fork (f , g))) = fork (map f , map g)"
    using fork_map_unzip[of f g] by simp
  then have "zip \<circ> (unzip \<circ> map (fork (f , g))) = zip \<circ> fork (map f , map g)"
    by simp
  then have "zip \<circ> unzip \<circ> map (fork (f, g)) = zip \<circ> fork (map f, map g)"
    by (simp add: comp_assoc)
  then have "id \<circ> map (fork (f, g)) = zip \<circ> fork (map f, map g)"
    by (simp add: zip_unzip_id)
  then show ?thesis
    by simp
qed

lemma map_fork_filter: "map (fork (f , g)) \<circ> filter (p \<circ> g) = filter (p \<circ> snd) \<circ> map (fork (f , g))"
  sorry

section \<open>A little theory\<close>

typedecl datum
type_synonym data = "datum list" 
type_synonym candidate = datum
typedecl val

locale Century_v1 =
  fixes candidates :: "data \<Rightarrow> candidate list"
    and eval :: "candidate \<Rightarrow> val"
    and good :: "val \<Rightarrow> bool"
    and ok :: "val \<Rightarrow> bool"
    and extend :: "datum \<Rightarrow> candidate list \<Rightarrow> candidate list"
    and modify :: "datum \<Rightarrow> val list \<Rightarrow> val list"
  assumes candidates_foldr_extend_empty: 
          "candidates = foldr extend []"
      and good_ok: 
          "\<And> v :: val. good v \<Longrightarrow> ok v"
      and ok_vals_extends_ok_vals: 
          "\<And> x :: datum. \<And> xs :: candidate list. 
                (filter (ok \<circ> eval) \<circ> extend x) xs = 
                (filter (ok \<circ> eval) \<circ> extend x \<circ> filter (ok \<circ> eval)) xs"
      and map_vals_extends_modify:
          "\<And> x. map eval \<circ> extend x = modify x \<circ> map eval"
begin

fun solutions :: "data \<Rightarrow> candidate list" where
  "solutions xs = (filter (good \<circ> eval) \<circ> candidates) xs"

lemma filter_good_value_ok_value:
  shows "filter (good \<circ> eval) xs = (filter (good \<circ> eval) \<circ> filter (ok \<circ> eval)) xs"
  by (induction xs) (auto simp add: good_ok)

fun extend' :: "datum \<Rightarrow> candidate list \<Rightarrow> candidate list" where
  "extend' x = filter (ok \<circ> eval) \<circ> extend x"

lemma new_solutions:
  shows "solutions = filter (good \<circ> eval) \<circ> foldr extend' []"
proof -
  have *: "filter (ok \<circ> eval) \<circ> (foldr extend []) = foldr extend' []"
    using fusion_foldr
              [of "filter (ok \<circ> eval)" "[]" "[]" extend extend', 
               OF filter.simps(1)]
    using ok_vals_extends_ok_vals by simp

  have "solutions = (filter (good \<circ> eval) \<circ> candidates)" 
    by auto
  also have "... = (filter (good \<circ> eval) \<circ> (foldr extend []))" 
    using candidates_foldr_extend_empty by simp
  also have "... = (filter (good \<circ> eval) \<circ> (filter (ok \<circ> eval) \<circ> (foldr extend [])))"
    using filter_good_value_ok_value by auto
  also have "... = (filter (good \<circ> eval) \<circ> foldr extend' [])" 
    using * by simp
  finally show "solutions = (filter (good \<circ> eval) \<circ> foldr extend' [])" .
qed

lemma "map (fork (id , eval)) \<circ> extend x = zip \<circ> cross (extend x , modify x) \<circ> unzip \<circ> map (fork (id , eval))"
proof -
  have "map (fork (id , eval)) \<circ> extend x = zip \<circ> fork (id , map eval) \<circ> extend x"
    using map_fork_zip[of id eval] by simp
  also have "... = zip \<circ> fork (extend x , map eval \<circ> extend x)"
    using fusion_fork[of id \<open>map eval\<close> \<open>extend x\<close>] by auto
  also have "... = zip \<circ> fork (extend x , modify x \<circ> map eval)"
    using map_vals_extends_modify by simp
  also have "... = zip \<circ> cross (extend x , modify x) \<circ> fork (id , map eval)"
    using cross_fork[of \<open>extend x\<close> id \<open>modify x\<close> \<open>map eval\<close>] by auto
  also have "... = zip \<circ> cross (extend x , modify x) \<circ> unzip \<circ> map (fork (id , eval))"
    using fork_map_unzip[of id eval] by auto
  finally show ?thesis .
qed

fun expand :: "datum \<Rightarrow> (datum \<times> val) list \<Rightarrow> (datum \<times> val) list" where 
  "expand x = filter (ok \<circ> snd) \<circ> zip \<circ> cross (extend x , modify x) \<circ> unzip"

fun solution':: "data \<Rightarrow> candidate list" where 
  "solution' xs = (map fst \<circ> filter (good \<circ> snd) \<circ> foldr expand []) xs"

end

section \<open>Making a century\<close>

type_synonym digit = int
type_synonym factor = "digit list"
type_synonym trm = "factor list"
type_synonym expression = "trm list"
type_synonym state = "int \<times> int \<times> int \<times> int"

fun eval_factor :: "factor \<Rightarrow> int" where
  "eval_factor f = foldl (\<lambda> n d. 10 * n + d) 0 f"

fun eval_term :: "trm \<Rightarrow> int" where
  "eval_term t = prod (map eval_factor t)"

fun eval_expression :: "expression \<Rightarrow> int" where
  "eval_expression e = sum (map eval_term e)"

(*
fun good :: "int \<Rightarrow> bool" where
  "good v = (v = 100)"

fun extend :: "digit \<Rightarrow> expression list \<Rightarrow> expression list" where
  "extend x [] = [[[[x]]]]"
| "extend x es = concat_map (glue x) es"

fun expressions :: "factor \<Rightarrow> expression list" where
  "expressions xs = foldr extend [] xs"

value "filter (good \<circ> eval_expression) (expressions [1,2,3,4,5,6,7,8,9])"
*)

fun good :: "int \<Rightarrow> state \<Rightarrow> bool" where
  "good c (k, f, t, e) = (f*t + e = c)"

fun ok :: "int \<Rightarrow> state \<Rightarrow> bool" where
  "ok c (k, f, t, e) = (f*t + e \<le> c)"

lemma good_ok: "good c s \<Longrightarrow> ok c s"
  by (induction s) auto

fun eval:: "expression \<Rightarrow> state " where
  "eval ((xs # xss) # xsss) = (10^(length xs), eval_factor xs, eval_term xss, eval_expression xsss)"

fun modify :: "digit \<Rightarrow> state \<Rightarrow> state list" where
 "modify x (k, f, t, e) = [(10*k, k*x + f, t, e), (10, x, f*t, e), (10, x, 1, f*t + e)]"

fun glue :: "digit \<Rightarrow> expression \<times> state \<Rightarrow> (expression \<times> state) list" where
  "glue x ((xs # xss) # xsss, (k , f , t, e)) = 
      [(((x # xs) # xss) # xsss, (10*k, k*x + f, t, e)),
       (([x] # xs # xss) # xsss, (10, x, f*t, e)),
       ([[x]] # (xs # xss) # xsss, (10, x, 1, f*t + e))]"

fun expand :: "int \<Rightarrow> digit \<Rightarrow> (expression \<times> state) list \<Rightarrow> (expression \<times> state) list" where
  "expand c x [] = [([[[x]]], (10, x, 1, 0))]"
| "expand c x ess = concat (map (filter (ok c \<circ> snd) \<circ> glue x) ess)"

fun solution :: "int \<Rightarrow> digit list \<Rightarrow> expression list" where
  "solution c xs = (map fst \<circ> filter (good c \<circ> snd) \<circ> foldr (expand c) []) xs"

value "solution 100 [1,2,3,4,5,6,7,8,9]"

end