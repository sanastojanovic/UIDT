theory BuildingATreeWithMinimumHeight
  imports Main
begin

datatype Tree = Leaf int | Fork Tree Tree

fun cost :: "Tree \<Rightarrow> int" where
"cost (Leaf x) = x" |
"cost (Fork u v) = 1 + max (cost u) (cost v)"

value "cost (Leaf 3)"
value "cost (Fork (Leaf 1) (Leaf 3))"
value "cost (Fork
  (Fork (Fork (Fork (Leaf 1) (Leaf 1)) (Leaf 3)) (Leaf 4))
  (Leaf 5))"

lemma cost_monotono: "cost (Fork t1 t2) > max (cost t1) (cost t2)"
  sorry

fun rollup :: "Tree list \<Rightarrow> Tree" where
"rollup [t] = t" |
"rollup (t1 # t2 # ts) = rollup ((Fork t1 t2) # ts)"

value "rollup [(Leaf 3), (Leaf 2)]"
value "rollup [(Fork (Leaf 1) (Leaf 3)), (Leaf 4)]"

fun prefixes :: "int \<Rightarrow> Tree list \<Rightarrow> Tree list list" where
"prefixes x [] = [[Leaf x]]" |
"prefixes x (t # ts) = (Leaf x # t # ts) # (map (\<lambda>ys. t # ys) (prefixes x ts))"

value "prefixes 3 [Leaf 2]"
value "prefixes 3 [(Fork (Leaf 1) (Leaf 3)), (Leaf 4)]"

(*Definisemo foldl1 koja radi isto kao foldl s tim sto foldl1 pretpostavlja da lista nije prazna (sto nam je i potrebno)*)
fun foldl1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"foldl1 f [x] = x" |
"foldl1 f (x # y # xs) = foldl f (f x y) xs"


value "foldl1 (\<lambda>x y. x + y::int) [1,2,3]"

fun less_eq_cost :: "Tree \<Rightarrow> Tree \<Rightarrow> bool" where
  "less_eq_cost (Leaf x) (Leaf y) = (x \<le> y)" |
  "less_eq_cost (Leaf x) (Fork u v) = True" |
  "less_eq_cost (Fork u v) (Leaf x) = False" |
  "less_eq_cost (Fork u1 v1) (Fork u2 v2) = ((cost u1 < cost u2) \<or>
                                            (cost u1 = cost u2 \<and> less_eq_cost v1 v2))"

definition less_cost :: "Tree \<Rightarrow> Tree \<Rightarrow> bool" (infix "\<prec>" 50) where
  "t1 \<prec> t2 \<longleftrightarrow> less_eq_cost t1 t2 \<and> \<not> less_eq_cost t2 t1"

fun cmp :: "Tree \<Rightarrow> Tree \<Rightarrow> Tree" where
  "cmp u v = (if u \<prec> v then u else v)"

value "cmp (Leaf 3) (Leaf 5)" 
value "cmp (Fork (Leaf 2) (Leaf 4)) (Fork (Leaf 1) (Leaf 3))" 

fun minBy :: "('a \<Rightarrow> Tree) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"minBy f (x # xs) = foldl (\<lambda>u v. if cmp (f u) (f v) = f u then u else v) x xs"

value "minBy (\<lambda>x. Leaf x) [1, 5, 3, 2]"

fun build_min_cost_tree :: "int list \<Rightarrow> Tree" where
"build_min_cost_tree [] = Leaf 0" |
"build_min_cost_tree [x] = Leaf x" |
"build_min_cost_tree xs = rollup (map Leaf xs)"

value "build_min_cost_tree [3, 1, 4, 2]"

end
