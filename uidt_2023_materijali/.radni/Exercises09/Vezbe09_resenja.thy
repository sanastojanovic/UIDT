
(*<*)
theory Vezbe09_resenja 
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Zasnivanje prirodnih brojeva.]\<close>

text \<open>Definisati algebarski tip podataka \<open>prirodni\<close> koji predstavlja prirodni broj.\<close>

datatype prirodni = 
    Nula ("\<zero>")
  | Sled prirodni

text \<open>Diskutovati o tipu \<open>prirodni\<close> i sledećim termovima.\<close>

typ prirodni

term "Nula"
term "Sled Nula"
term "Sled (Sled Nula)"


text \<open>Definisati skraćenice za prirodne brojeve \<open>\<one>, \<two>, \<three>\<close>.\<close>

abbreviation jedan :: prirodni ("\<one>") where
  "\<one> \<equiv> Sled \<zero>"

abbreviation dva :: prirodni ("\<two>") where
  "\<two> \<equiv> Sled \<one>"

abbreviation tri :: prirodni ("\<three>") where
  "\<three> \<equiv> Sled \<two>"

text \<open>Primitivnom rekurzijom definisati operaciju sabiranja. Uvesti levo 
      asocijativni operator \<open>\<oplus>\<close> za operaciju sabiranja.\<close>

primrec saberi :: "prirodni \<Rightarrow> prirodni \<Rightarrow> prirodni" (infixl "\<oplus>" 100)where
  "\<zero> \<oplus> b = b"
| "(Sled a) \<oplus> b = Sled (a \<oplus> b)"

text \<open>Testirati funkciju sabiranjem nekih skraćenica za prirodne brojeve.\<close>

value "\<one> \<oplus> \<two> \<noteq> \<three>"

text \<open>Pokazati da je sabiranje asocijativno.\<close>

lemma saberi_asoc:
  shows "a \<oplus> (b \<oplus> c) = a \<oplus> b \<oplus> c"
  by (induction a) auto

text \<open>Pokazati da je sabiranje komutativno.\\
     \<open>Savet\<close>: Potrebno je pokazati pomoćne lemu.\<close>

lemma saberi_Nula_desno[simp]:
  shows "a \<oplus> \<zero> = a"
  by (induction a) auto

lemma saberi_Sled_desno[simp]:
  shows "a \<oplus> Sled b = Sled (a \<oplus> b)"
  by (induction a) auto

lemma saberi_kom:
  shows "a \<oplus> b = b \<oplus> a"
  by (induction a) auto

lemma saberi_kom_isar:
  shows "a \<oplus> b = b \<oplus> a"
proof (induction a)
  case Nula
  have "\<zero> \<oplus> b = b" by (rule saberi.simps(1))
  also have "b = b \<oplus> \<zero>" by (rule saberi_Nula_desno[symmetric])
  finally show ?case .
next
  case (Sled a)
  have "Sled a \<oplus> b = Sled (a \<oplus> b)" by (rule saberi.simps(2))
  also have "... = Sled (b \<oplus> a)" by (subst Sled, rule refl)
  also have "... = b \<oplus> Sled a" by (rule saberi_Sled_desno[symmetric])
  finally show ?case .
qed

text \<open>Primitivnom rekurzijom definisati operaciju množenja. Uvesti levo 
      asocijativni operator \<open>\<otimes>\<close> za operaciju množenja.\<close>

primrec pomnozi :: "prirodni \<Rightarrow> prirodni \<Rightarrow> prirodni" (infixl "\<otimes>" 101) where
  "pomnozi \<zero> b = \<zero>"
| "pomnozi (Sled a) b = a \<otimes> b \<oplus> b"

text \<open>Pokazati komutativnost množenja.\\
     \<open>Savet\<close>: Pokazati pomoćne lemme.\<close>

lemma pomnozi_Nula_desno[simp]:
  shows "a \<otimes> \<zero> = \<zero>"
  by (induction a) auto

lemma pomnozi_Sled_desno[simp]:
  shows "a \<otimes> Sled b = a \<oplus> a \<otimes> b"
  by (induction a) (auto simp add: saberi_asoc)

lemma pomnozi_kom:
  shows "a \<otimes> b = b \<otimes> a"
  by (induction a) (auto simp add: saberi_kom)

text \<open>Pokazati da je množenje asocijativno.\<close>

lemma saberi_pomnozi_distrib_desno:
  shows "(a \<oplus> b) \<otimes> c = a \<otimes> c \<oplus> b \<otimes> c"
  by (induction a) (auto simp add: pomnozi_kom saberi_asoc)

lemma pomnozi_asoc:
  shows "a \<otimes> (b \<otimes> c) = a \<otimes> b \<otimes> c"
  by (induction a) (auto simp add: saberi_pomnozi_distrib_desno)

text \<open>Primitivnom rekurzijom definisati operaciju stepenovanja. Uvesti desno 
      asocijativni operator \<open>\<Zcat>\<close> za operaciju stepenovanja.\<close>

primrec stepenuj :: "prirodni \<Rightarrow> prirodni \<Rightarrow> prirodni" (infixr "\<Zcat>" 102) where
  "a \<Zcat> \<zero> = \<one>"
| "a \<Zcat> (Sled n) = a \<otimes> a \<Zcat> n"

value "\<two> \<Zcat> \<zero>"
value "\<two> \<Zcat> \<two>"

text \<open>Pokazati da važi: $a^1 = a$.\<close>

lemma stepenuj_jedan:
  shows "a \<Zcat> \<one> = a"
  by auto

text \<open>Pokazati da važi: $a^{(n+m)} = a^n b^m$.\<close>

lemma stepenuj_na_zbir[simp]:
  shows "a \<Zcat> (n \<oplus> m) = a \<Zcat> n \<otimes> a \<Zcat> m"
  by (induction n) (auto simp add: pomnozi_asoc)

text \<open>Pokazati da važi: $a^{nm} = a^{n^m}$.\<close>

lemma stepenuj_jedinicu[simp]:
  shows "\<one> \<Zcat> n = \<one>"
  by (induction n) auto

lemma stepenuj_proizvod[simp]:
  shows "(a \<otimes> b) \<Zcat> n = a \<Zcat> n \<otimes> b \<Zcat> n"
  by (induction n) (auto, metis pomnozi_asoc pomnozi_kom)

lemma stepenuj_na_proizvod:
  shows "a \<Zcat> (n \<otimes> m) = (a \<Zcat> n) \<Zcat> m"
  by (induction n) (auto simp add: pomnozi_kom)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Dodatni primeri.]\<close>

text \<open>Pokazati sledeće teoreme u Isar-u. Kao dodatan izazov, dozvoljeno je korišćenje samo 
      primenjivanje pravila \<open>rule\<close> i \<open>subst\<close> za dokazivanje među koraka, tj. bilo
      kakva automatizacija (\<open>simp, auto, metis, blast, force, fastforce, sladgehammer, ...\<close>) 
      je zabranjena.\<close>

lemma "a \<oplus> \<zero> = a"
proof (induction a)
  case Nula
  have "\<zero> \<oplus> \<zero> = \<zero>" by (rule saberi.simps(1))
  then show ?case .
next
  case (Sled a)
  have "Sled a \<oplus> \<zero> = Sled (a \<oplus> \<zero>)" by (rule saberi.simps(2))
  also have "... = Sled a" by (subst saberi_Nula_desno, rule refl)
  finally show ?case .
qed

lemma "a \<otimes> (Sled b) = a \<otimes> b \<oplus> a"
proof (induction a)
  case Nula
  have "\<zero> \<otimes> Sled b = \<zero>" by (rule pomnozi.simps(1))
  also have "... = \<zero> \<otimes> b" by (rule pomnozi.simps(1)[symmetric])
  also have "... = \<zero> \<oplus> \<zero> \<otimes> b" by (rule saberi.simps(1)[symmetric])
  also have "... = \<zero> \<otimes> b \<oplus> \<zero>" by (rule saberi_kom)
  finally show ?case .
next
  case (Sled a)
  thm pomnozi.simps(2)
  have "Sled a \<otimes> Sled b = Sled b \<otimes> Sled a" by (rule pomnozi_kom)
  also have "... = b \<otimes> Sled a \<oplus> Sled a" by (rule pomnozi.simps(2))
  also have "... = Sled a \<otimes> b \<oplus> Sled a" by (subst pomnozi_kom, rule refl)
  finally show ?case .
qed

lemma "(a \<oplus> b) \<otimes> c = a \<otimes> c \<oplus> b \<otimes> c"
proof (induction a)
  case Nula
  have "(\<zero> \<oplus> b) \<otimes> c = b \<otimes> c" by (subst saberi.simps(1), rule refl)
  thm saberi.simps(1)[symmetric]
  also have "... = \<zero> \<oplus> b \<otimes> c" by (rule saberi.simps(1)[symmetric])
  also have "... = \<zero> \<otimes> c \<oplus> b \<otimes> c" by (subst pomnozi.simps(1)[symmetric], rule refl)
  finally show ?case .
next
  case (Sled a)
  have "(Sled a \<oplus> b) \<otimes> c = Sled (a \<oplus> b) \<otimes> c" by (subst saberi.simps(2), rule refl)
  also have "... = (a \<oplus> b) \<otimes> c \<oplus> c" by (rule pomnozi.simps(2))
  also have "... = a \<otimes> c \<oplus> b \<otimes> c \<oplus> c" by (subst Sled, rule refl)
  also have "... = a \<otimes> c \<oplus> (b \<otimes> c \<oplus> c)" by (rule saberi_asoc[symmetric])
  also have "... = b \<otimes> c \<oplus> c \<oplus> a \<otimes> c" by (rule saberi_kom) 
  also have "... = b \<otimes> c \<oplus> (c \<oplus> a \<otimes> c)" by (rule saberi_asoc[symmetric])
  also have "... = c \<oplus> a \<otimes> c \<oplus> b \<otimes> c" by (rule saberi_kom)
  also have "... = a \<otimes> c \<oplus> c \<oplus> b \<otimes> c" by (subst saberi_kom, rule refl)
  also have "... = Sled a \<otimes> c \<oplus> b \<otimes> c" by (subst pomnozi.simps(2)[symmetric], rule refl)
  finally show ?case .
qed

lemma "a \<otimes> b \<otimes> c = a \<otimes> (b \<otimes> c)"
proof (induction a)
  case Nula
  thm pomnozi.simps(1)
  have "\<zero> \<otimes> b \<otimes> c = \<zero> \<otimes> c" by (subst pomnozi.simps(1), rule refl)
  also have "... = \<zero>" by (rule pomnozi.simps(1))
  also have "... = \<zero> \<otimes> (b \<otimes> c)" by (rule pomnozi.simps(1)[symmetric])
  finally show ?case .
next
  case (Sled a)
  have "Sled a \<otimes> b \<otimes> c = (a \<otimes> b \<oplus> b) \<otimes> c" by (subst pomnozi.simps(2), rule refl)
  also have "... = a \<otimes> b \<otimes> c \<oplus> b \<otimes> c" by (rule saberi_pomnozi_distrib_desno)
  also have "... = a \<otimes> (b \<otimes> c) \<oplus> b \<otimes> c" by (subst Sled, rule refl)
  also have "... = Sled a \<otimes> (b \<otimes> c)" by (rule pomnozi.simps(2)[symmetric])
  finally show ?case .
qed

lemma "a \<otimes> b = b \<otimes> a"
proof (induction a)
  case Nula
  have "\<zero> \<otimes> b = \<zero>" by (rule pomnozi.simps(1))
  also have "... = b \<otimes> \<zero>" by (rule pomnozi_Nula_desno[symmetric])
  finally show ?case .
next
  case (Sled a)
  have "Sled a \<otimes> b = a \<otimes> b \<oplus> b" by (rule pomnozi.simps(2))
  also have "... = b \<otimes> a \<oplus> b" by (subst Sled, rule refl)
  also have "... = b \<oplus> b \<otimes> a" by (rule saberi_kom)
  also have "... = b \<otimes> Sled a" by (rule pomnozi_Sled_desno[symmetric])
  finally show ?case .
qed

lemma "a \<otimes> (b \<oplus> c) = a \<otimes> b \<oplus> a \<otimes> c"
proof (induction a)
  case Nula
  have "\<zero> \<otimes> (b \<oplus> c) = \<zero>" by (rule pomnozi.simps(1))
  also have "... = \<zero> \<otimes> c" by (rule pomnozi.simps(1)[symmetric])
  also have "... = \<zero> \<oplus> \<zero> \<otimes> c" by (rule saberi.simps(1)[symmetric])
  also have "... = \<zero> \<otimes> b \<oplus> \<zero> \<otimes> c" by (subst pomnozi.simps(1)[symmetric], rule refl)
  finally show ?case .
next
  case (Sled a)
  have "Sled a \<otimes> (b \<oplus> c) = a \<otimes> (b \<oplus> c) \<oplus> (b \<oplus> c)" by (rule pomnozi.simps(2))
  also have "... = a \<otimes> b \<oplus> a \<otimes> c \<oplus> (b \<oplus> c)" by (subst Sled, rule refl)
  also have "... = a \<otimes> b \<oplus> a \<otimes> c \<oplus> b \<oplus> c" by (rule saberi_asoc)
  also have "... = a \<otimes> c \<oplus> a \<otimes> b \<oplus> b \<oplus> c" by (subst saberi_kom, rule refl)
  also have "... = a \<otimes> c \<oplus> (a \<otimes> b \<oplus> b) \<oplus> c" by (subst saberi_asoc, rule refl)
  also have "... = a \<otimes> b \<oplus> b \<oplus> a \<otimes> c \<oplus> c" by (subst saberi_kom, rule refl) 
  also have "... = Sled a \<otimes> b \<oplus> a \<otimes> c \<oplus> c" by (subst pomnozi.simps(2)[symmetric], rule refl)
  also have "... = Sled a \<otimes> b \<oplus> (a \<otimes> c \<oplus> c)" by (subst saberi_asoc, rule refl)
  also have "... = a \<otimes> c \<oplus> c \<oplus> Sled a \<otimes> b" by (subst saberi_kom, rule refl)
  also have "... = Sled a \<otimes> c \<oplus> Sled a \<otimes> b" by (subst pomnozi.simps(2)[symmetric], rule refl)
  also have "... = Sled a \<otimes> b \<oplus> Sled a \<otimes> c" by (rule saberi_kom)
  finally show ?case .
qed

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
