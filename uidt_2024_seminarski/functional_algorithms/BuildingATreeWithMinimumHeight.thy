theory BuildingATreeWithMinimumHeight
  imports Main
begin

datatype Tree = Leaf nat | Fork Tree Tree

fun cost :: "Tree \<Rightarrow> nat" where
"cost (Leaf x) = x" |
"cost (Fork u v) = 1 + max (cost u) (cost v)"

value "cost (Leaf 3)"
value "cost (Fork (Leaf 1) (Leaf 3))"
value "cost (Fork
  (Fork (Fork (Fork (Leaf 1) (Leaf 1)) (Leaf 3)) (Leaf 4))
  (Leaf 5))"

lemma cost_monotono: "cost (Fork t1 t2) > max (cost t1) (cost t2)"
  by auto

lemma cost_nonnegative[simp]: "0 \<le> cost t"
proof (induction t)
  case (Leaf x)
  then show ?case by simp
next
  case (Fork t1 t2)
  then show ?case by simp
qed

lemma cost_Fork_strict[simp]: "cost (Fork t1 t2) > cost t1 \<and> cost (Fork t1 t2) > cost t2"
proof -
  have "cost (Fork t1 t2) = 1 + max (cost t1) (cost t2)" by simp
  moreover have "max (cost t1) (cost t2) \<ge> cost t1" by simp
  moreover have "max (cost t1) (cost t2) \<ge> cost t2" by simp
  ultimately show "cost (Fork t1 t2) > cost t1 \<and> cost (Fork t1 t2) > cost t2" by linarith
qed

fun rollup :: "Tree list \<Rightarrow> Tree" where
"rollup [t] = t" |
"rollup (t1 # t2 # ts) = rollup ((Fork t1 t2) # ts)"

value "rollup [(Leaf 3), (Leaf 2)]"
value "rollup [(Fork (Leaf 1) (Leaf 3)), (Leaf 4)]"

lemma rollup_preserves_cost[simp]: "t \<in> set ts \<Longrightarrow> cost (rollup ts) \<ge> cost t"
proof (induction ts arbitrary: t rule: rollup.induct)
  case (1 t)
  then show ?case by simp
      next
        case (2 t1 t2 ts)
        then show ?case
        proof (cases "t = t1 \<or> t = t2")
          case True
          hence "cost (rollup (Fork t1 t2 # ts)) \<ge> cost t"  by (meson "2.IH" cost_Fork_strict dual_order.trans linorder_not_less list.set_intros(1) nat_le_linear)
          thus ?thesis by simp
              next
                case False
                hence "t \<in> set ts" using 2 by auto
                hence "cost (rollup ts) \<ge> cost t" by (meson "2.IH" cost_Fork_strict dual_order.trans list.set_intros(1) order_less_le)
                moreover have "cost (rollup (Fork t1 t2 # ts)) \<ge> cost (rollup ts)" by (meson "2.IH" cost_Fork_strict dual_order.trans list.set_intros(1) order_less_le)
                ultimately show ?thesis by auto
              qed
            next
              case 3
              then show ?case by simp
                  qed

fun prefixes :: "nat \<Rightarrow> Tree list \<Rightarrow> Tree list list" where
"prefixes x [] = [[Leaf x]]" |
"prefixes x (t # ts) = (Leaf x # t # ts) # (map (\<lambda>ys. t # ys) (prefixes x ts))"

value "prefixes 3 [Leaf 2]"
value "prefixes 3 [(Fork (Leaf 1) (Leaf 3)), (Leaf 4)]"

fun foldl1 :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"foldl1 f [x] = x" |
"foldl1 f (x # y # xs) = foldl f (f x y) xs"

value "foldl1 (\<lambda>x y. x + y::int) [1,2,3]"

lemma foldl1_correct: "foldl1 f (x # xs) = foldl f x xs"
  by (induction xs arbitrary: x) simp_all

fun less_eq_cost :: "Tree \<Rightarrow> Tree \<Rightarrow> bool" where
  "less_eq_cost (Leaf x) (Leaf y) = (x \<le> y)" |
  "less_eq_cost (Leaf x) (Fork u v) = True" |
  "less_eq_cost (Fork u v) (Leaf x) = False" |
  "less_eq_cost (Fork u1 v1) (Fork u2 v2) = ((cost u1 < cost u2) \<or>
                                            (cost u1 = cost u2 \<and> less_eq_cost v1 v2))"

lemma less_eq_cost_refl: "less_eq_cost t t"
  by (induction t) simp_all

definition less_cost :: "Tree \<Rightarrow> Tree \<Rightarrow> bool" (infix "\<prec>" 50) where
  "t1 \<prec> t2 \<longleftrightarrow> less_eq_cost t1 t2 \<and> \<not> less_eq_cost t2 t1"

lemma less_cost_irrefl: "\<not> (t \<prec> t)"
  by (simp add: less_cost_def)

fun cmp :: "Tree \<Rightarrow> Tree \<Rightarrow> Tree" where
  "cmp u v = (if u \<prec> v then u else v)"

value "cmp (Leaf 3) (Leaf 5)" 
value "cmp (Fork (Leaf 2) (Leaf 4)) (Fork (Leaf 1) (Leaf 3))" 

lemma cmp_correct: "cmp t1 t2 = (if t1 \<prec> t2 then t1 else t2)"
  by simp

fun minBy :: "('a \<Rightarrow> Tree) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"minBy f (x # xs) = foldl (\<lambda>u v. if cmp (f u) (f v) = f u then u else v) x xs"

value "minBy (\<lambda>x. Leaf x) [1, 5, 3, 2]"

fun build_min_cost_tree :: "nat list \<Rightarrow> Tree" where
"build_min_cost_tree [] = Leaf 0" |
"build_min_cost_tree [x] = Leaf x" |
"build_min_cost_tree xs = rollup (map Leaf xs)"

value "build_min_cost_tree [3, 1, 4, 2]"


lemma build_min_cost_tree_cost: "set (map Leaf xs) \<subseteq> set (flatten t) \<Longrightarrow> cost (build_min_cost_tree xs) \<le> cost t"
  sorry

end
