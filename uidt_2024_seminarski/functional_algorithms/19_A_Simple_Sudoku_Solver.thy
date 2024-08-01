theory "19_A_Simple_Sudoku_Solver"
  imports Main

(* Dejana Kop 91/2019 *)

begin

type_synonym 'a Row = "'a list"
type_synonym 'a Matrix = "'a Row list"
type_synonym Digit = "char"
type_synonym Grid = "Digit Matrix"
type_synonym Choices = "Digit list"

definition digits :: "Digit list" where
  "digits \<equiv> ''123456789''"

definition blank :: "Digit \<Rightarrow> bool" where
  "blank c \<equiv> (c = (CHR ''0''))"

(* CHOICES *)

definition choice :: "Digit \<Rightarrow> Choices" where 
  "choice d = (if blank d then digits else [d])"

definition choices :: "Grid \<Rightarrow> Choices Matrix"  where 
  "choices = map (map choice)"

(* EXPAND *)

fun cp :: "'a list list \<Rightarrow> 'a list list" where 
  "cp [] = [[]]"
| "cp (xs # xss) = [(x # ys) . x <- xs, ys <- cp xss]"

value "cp [''12'', ''3'', ''45'']"

definition expand :: "Choices Matrix \<Rightarrow> Grid list"  where 
  "expand = cp \<circ> map cp"

(* VALID *)

(*fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "all p [] = True"
| "all p (x # xs) = (p x) \<and> all p xs"*)

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "all p [] = True"
| "all p (x # xs) = ((p x) \<and> (all p xs))"

fun check where
  "check x [] = True"
| "check x (xx # xs) = ((x = xx) \<and> (check x xs))"

fun nodups :: "'a Row \<Rightarrow> bool" where 
  "nodups [] = True"
| "nodups (x # xs) = ((check x xs) \<and> (nodups xs))"

definition rows :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "rows = id"

fun cols :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "cols [] = []"
| "cols [xs] = [[x] . x <- xs]"
| "cols (xs # xss) = map2 (Cons) xs (cols xss)"

fun group :: "'a list \<Rightarrow> 'a Matrix" where
  "group [] = []"
| "group xs = take 3 xs # group (drop 3 xs)"

definition ungroup :: "'a Matrix \<Rightarrow> 'a list" where
  "ungroup = concat"

definition boxs :: "'a Matrix \<Rightarrow> 'a Matrix" where 
  "boxs = map ungroup \<circ> ungroup \<circ> map cols \<circ> group \<circ> map group"

definition valid :: "Grid \<Rightarrow> bool" where
  "valid g \<equiv>
    (all nodups (rows g)) \<and> 
    (all nodups (cols g)) \<and>
    (all nodups (boxs g))
  "

(* SOLVE *)

(* definition solve :: "Grid \<Rightarrow> Grid" where 
  "solve = filter valid \<circ> expand \<circ> choices" *)

(* LEMMAS *)

lemma group_ungroup: "group \<circ> ungroup = id"
  oops

lemma rows_id: "rows \<circ> rows = id"
  oops

lemma cols_id: "cols \<circ> cols = id"
  oops

lemma boxs_id: "boxs \<circ> boxs = id"
  oops

lemma expand_rows: "map rows \<circ> expand = expand \<circ> rows" (*19.1*)
  oops

lemma expand_cols: "map cols \<circ> expand = expand \<circ> cols" (*19.2*)
  oops

lemma expand_boxs: "map boxs \<circ> expand = expand \<circ> boxs" (*19.3*)
  oops

(* PRUNING *)



end