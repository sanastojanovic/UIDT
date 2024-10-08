
(*<*)
theory Vezbe07_resenja 
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Tip: list.]\<close>

text \<open>Diskutovati o sledećim termovima i vrednostima.\<close>

term "[]"
term "1 # 2 # []"
term "(1::nat) # 2 # []"
term "[1, 2]"
term "[1::nat, 2]"

value "[1..5]"
value "[1..<5]"

term sum_list
value "sum_list [1..<5]"

term map
term "\<lambda> x. f x"
value "map (\<lambda> x. x^2) [1..<5]"
value "sum_list (map (\<lambda> x. x^2) [1..<5])"

value "\<Sum> x \<leftarrow> [1..<5]. x^2"

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Sumiranje nizova preko listi.]\<close>

text \<open>Pokazati da važi: $1 + 2^2 + \ldots + n^2 = \frac{n (n + 1) (2n + 1)}{6}$.\<close>

primrec zbir_kvadrata :: "nat \<Rightarrow> nat" where
  "zbir_kvadrata 0 = 0"
| "zbir_kvadrata (Suc n) = zbir_kvadrata n + (Suc n) ^ 2"

text \<open>Definisati funkciju \<open>zbir_kvadrata' :: nat \<Rightarrow> nat\<close> preko definicije,
      koja računa levu stranu jednakosti pomoću liste i funkcijama nad listama.\<close>

definition zbir_kvadrata' :: "nat \<Rightarrow> nat" where
  "zbir_kvadrata' n = sum_list (map (\<lambda> x. x^2) [1..<Suc n])"

text \<open>Pokazati da su ove dve funkcije ekvivalentne.\<close>

lemma "zbir_kvadrata n = zbir_kvadrata' n"
  by (induction n) (auto simp add: zbir_kvadrata'_def)

text \<open>Pokazati automatski da je \<open>zbir_kvadrata n = n * (n + 1) * (2 * n + 1) div 6\<close>.\\
      \<open>Savet\<close>: Razmotriti leme koje se koriste u Isar verziji dokaza i dodati ih u \<open>simp\<close>.\<close>

lemma "zbir_kvadrata n = n * (n + 1) * (2 * n + 1) div 6"
  by (induction n) (auto simp add: algebra_simps power2_eq_square)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Algebarski tip podataka: lista.]\<close>

text \<open>Definisati polimorfan algebarski tip podataka \<open>'a lista\<close>
      koji predstavlja listu elemenata polimorfong tipa \<open>'a\<close>.\<close>

datatype 'a lista = Prazna
                  | Dodaj 'a "'a lista"

term "Dodaj (1::nat) (Dodaj 2 (Dodaj 3 Prazna))"

text \<open>Definisati funkcije 
      \<open>duzina' :: 'a lista \<Rightarrow> nat\<close>, 
      \<open>nadovezi' :: 'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista\<close>,
      \<open>obrni' :: 'a lista \<Rightarrow> 'a lista\<close>
      primitivnom rekurzijom koje računaju
      dužinu liste, nadoveziju i obrću liste tipa \<open>'a lista\<close>.\<close>

primrec duzina' :: "'a lista \<Rightarrow> nat" where
  "duzina' Prazna = 0"
| "duzina' (Dodaj _ xs) = 1 + duzina' xs"

primrec nadovezi' :: "'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista" where
  "nadovezi' Prazna ys = ys"
| "nadovezi' (Dodaj x xs) ys = Dodaj x (nadovezi' xs ys)"

primrec obrni' :: "'a lista \<Rightarrow> 'a lista" where
  "obrni' Prazna = Prazna"
| "obrni' (Dodaj x xs) = nadovezi' (obrni' xs) (Dodaj x Prazna)"

text \<open>Definisati funkciju \<open>duzina :: 'a list \<Rightarrow> nat\<close> primitivnom rekurzijom 
      koja računa dužinu liste tipa \<open>'a list\<close>.
      Pokazati da su \<open>duzina\<close> i \<open>length\<close> ekvivalentne funkcije.\<close>

primrec duzina :: "'a list \<Rightarrow> nat" where
  "duzina [] = 0"
| "duzina (x # xs) = 1 + duzina xs"

lemma duzina_length:
  shows "duzina xs = length xs"
  by (induction xs) auto

text \<open>Definisati funkciju \<open>prebroj :: ('a::equal) \<Rightarrow> 'a list \<Rightarrow> nat\<close> primitivnom rekurzijom 
      koja računa koliko se puta javlja element tipa \<open>'a::equal\<close> u listi tipa \<open>('a::equal) list\<close>. 
      Pokazati da je \<open>prebroj a xs \<le> length xs\<close>.\<close>

primrec prebroj :: "('a::equal) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "prebroj a []= 0"
| "prebroj a (x # xs)= (if a = x then 1 + prebroj a xs else prebroj a xs)"

lemma "prebroj a xs \<le> length xs"
  by (induction xs) auto

term count_list

text \<open>Definisati funkciju \<open>sadrzi :: ('a::equal) \<Rightarrow> 'a list \<Rightarrow> bool\<close> primitivnom rekurzijom
      koja ispituje da li se element tipa \<open>'a::equal\<close> javlja u listi tipa \<open>('a::equal) list\<close>.
      Pokazati da je \<open>sadrzi a xs = a \<in> set xs\<close>\<close>

primrec sadrzi :: "('a::equal) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sadrzi a [] \<longleftrightarrow> False"
| "sadrzi a (x # xs) \<longleftrightarrow> a = x \<or> sadrzi a xs"

lemma "sadrzi a xs \<longleftrightarrow> a \<in> set xs"
  by (induction xs) auto

text \<open>Definisati funkciju \<open>skup :: 'a list \<Rightarrow> 'a set\<close> primitivnom rekurzijom
      koja vraća skup tipa \<open>'a set\<close> koji je sačinjen od elemenata liste tipa \<open>'a list\<close>.
      Pokazati da je \<open>skup xs = set xs\<close>.\<close>

primrec skup :: "'a list \<Rightarrow> 'a set" where
  "skup [] = {}"
| "skup (x # xs) = {x} \<union> skup xs"

text \<open>Definisati funkciju \<open>nadovezi :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> primitivnom rekurzijom
      koja nadovezuje jednu listu na drugu tipa \<open>'a list\<close>.
      Pokazati da je ekvivalentna ugrađenoj funkciji \<open>append\<close> 
      ili infiksom operatoru \<open>@\<close>.\<close>

primrec nadovezi :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "nadovezi [] ys = ys"
| "nadovezi (x # xs) ys = x # nadovezi xs ys"

lemma nadovezi_append:
  shows "nadovezi xs ys = xs @ ys"
  by (induction xs) auto

text \<open>Formulisati i pokazati da je dužina dve nedovezane liste, zbir dužina pojedinačnih listi.\\
      Orediti i dokazati osobine za funkcije \<open>skup\<close> i \<open>nadovezi\<close>, kao i za \<open>sadrzi\<close> i \<open>nadovezi\<close>.\<close>

lemma duzina_nadovezi:
  shows "duzina (nadovezi xs ys) = duzina xs + duzina ys"
  by (induction xs) auto

lemma skup_nadovezi:
  shows "skup (nadovezi xs ys) = skup xs \<union> skup ys"
  by (induction xs) auto

lemma sadrzi_nadovezi:
  shows "sadrzi a (nadovezi xs ys) = sadrzi a xs \<or> sadrzi a ys"
  by (induction xs) auto

text \<open>Definisati funkicju \<open>obrni :: 'a list \<Rightarrow> 'a list\<close> primitivnom rekurzijom
      koja obrće listu tipa \<open>'a list\<close>. 
      Pokazati da funkcija je \<open>obrni\<close> ekvivalentna funkciji \<open>rev\<close>.
      Nakon toga pokazati da je dvostruko obrnuta lista
      ekvivalentna početnoj listi.\\
      \<open>Napomena\<close>: Pri definisanju funkcije \<open>obrni\<close> nije dozvoljeno 
                  koristiti operator nadovezivanje \<open>@\<close>.\\
      \<open>Savet\<close>: Potrebno je definisati pomoćne leme.\<close>

primrec obrni :: "'a list \<Rightarrow> 'a list" where
  "obrni [] = []"
| "obrni (x # xs) = nadovezi (obrni xs) [x]"

lemma obrni_rev: 
  shows "obrni xs = rev xs"
  by (induction xs) (auto simp add: nadovezi_append)

lemma nadovezi_asoc:
  shows "nadovezi (nadovezi xs ys) zs = nadovezi xs (nadovezi ys zs)"
  by (induction xs) auto

lemma nadovezi_Nil_desno [simp]:
  shows "nadovezi xs [] = xs"
  by (induction xs) auto

lemma obrni_nadovezi [simp]: 
  shows "obrni (nadovezi xs ys) = nadovezi (obrni ys) (obrni xs)"
  by (induction xs) (auto simp add: nadovezi_asoc)

lemma obrni_obrni_id: "obrni (obrni xs) = xs"
  by (induction xs) auto

text \<open>Definisati funkciju \<open>snoc :: 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> koja dodaje element 
      na kraj liste, i funkciju \<open>rev_snoc :: 'a list \<Rightarrow> 'a list\<close> koja uz pomoć 
      funkcije \<open>snoc\<close> obrće elemente liste. Da li \<open>rev_snoc\<close> popravlja složenost
      obrtanja liste?\<close>

primrec snoc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "snoc a [] = [a]"
| "snoc a (x # xs) = x # snoc a xs"

primrec rev_snoc :: "'a list \<Rightarrow> 'a list" where
  "rev_snoc [] = []"
| "rev_snoc (x # xs) = snoc x (rev_snoc xs)"

text \<open>Definisati funkciju \<open>itrev\<close> koja obrće listu iterativno.\\
      \<open>Savet\<close>: Koristiti pomoćnu listu.\<close>

primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"

text \<open>Pokazati da je funkcija \<open>itrev\<close> ekvivalentna ugrađenoj
      funkciji \<open>rev\<close>, kada je inicijalna pomoćna lista prazna.\<close>

lemma itrev_rev_append:
  shows "itrev xs ys = rev xs @ ys"
  by (induction xs arbitrary: ys) auto

lemma itrev_rev:
  shows "itrev xs [] = rev xs"
  by (induction xs) (auto simp add: itrev_rev_append)

text \<open>Pomoću funkcije \<open>fold\<close> opisati obrtanje liste.
      Pokazati ekvivalentnost funkciji \<open>itrev\<close> sa obrtanjem liste preko \<open>fold\<close>-a.\<close>

term fold

lemma fold_Cons_append:
  shows "fold (#) xs ys @ zs = fold (#) xs (ys @ zs)"
  by (induction xs arbitrary: ys zs) auto

lemma itrev_fold_Cons:
  shows "itrev xs ys = fold (#) xs ys"
  by (induction xs arbitrary: ys) (auto simp add: itrev_rev_append fold_Cons_append)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
