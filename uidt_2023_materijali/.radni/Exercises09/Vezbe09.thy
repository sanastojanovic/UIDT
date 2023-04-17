
(*<*)
theory MyTheory
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Zasnivanje prirodnih brojeva.]\<close>

text \<open>Definisati algebarski tip podataka \<open>prirodni\<close> koji predstavlja prirodni broj.\<close>

datatype prirodni = undef

text \<open>Diskutovati o tipu \<open>prirodni\<close> i sledećim termovima.\<close>

typ prirodni

term "Nula"
term "Sled Nula"
term "Sled (Sled Nula)"


text \<open>Definisati skraćenice za prirodne brojeve \<open>\<one>, \<two>, \<three>\<close>.\<close>

abbreviation jedan :: prirodni ("\<one>") where
  "\<one> \<equiv> undefined"

abbreviation dva :: prirodni ("\<two>") where
  "\<two> \<equiv> undefined"

abbreviation tri :: prirodni ("\<three>") where
  "\<three> \<equiv> undefined"

text \<open>Primitivnom rekurzijom definisati operaciju sabiranja. Uvesti levo 
      asocijativni operator \<open>\<oplus>\<close> za operaciju sabiranja.\<close>

fun saberi (infixl "\<oplus>" 100) where
  "a \<oplus> b = undefined"

text \<open>Testirati funkciju sabiranjem nekih skraćenica za prirodne brojeve.\<close>

text \<open>Pokazati da je sabiranje asocijativno.\<close>

lemma saberi_asoc:
  shows "a \<oplus> (b \<oplus> c) = a \<oplus> b \<oplus> c"
  (*<*) oops (*>*)

text \<open>Pokazati da je sabiranje komutativno.\\
     \<open>Savet\<close>: Potrebno je pokazati pomoćne lemu.\<close>

lemma saberi_kom:
  shows "a \<oplus> b = b \<oplus> a"
  (*<*) oops (*>*)

lemma saberi_kom_isar:
  shows "a \<oplus> b = b \<oplus> a"
  (*<*) oops (*>*)

text \<open>Primitivnom rekurzijom definisati operaciju množenja. Uvesti levo 
      asocijativni operator \<open>\<otimes>\<close> za operaciju množenja.\<close>

fun pomnozi (infixl "\<otimes>" 101) where
  "a \<otimes> b = undefined"

text \<open>Pokazati komutativnost množenja.\\
     \<open>Savet\<close>: Pokazati pomoćne lemme.\<close>

lemma pomnozi_kom:
  shows "a \<otimes> b = b \<otimes> a"
  (*<*) oops (*>*)

text \<open>Pokazati da je množenje asocijativno.\<close>

lemma pomnozi_asoc:
  shows "a \<otimes> (b \<otimes> c) = a \<otimes> b \<otimes> c"
  (*<*) oops (*>*)

text \<open>Primitivnom rekurzijom definisati operaciju stepenovanja. Uvesti levo 
      asocijativni operator \<open>\<Zcat>\<close> za operaciju stepenovanja.\<close>

fun stepenuj (infixl "\<Zcat>" 102) where
  "a \<Zcat> b = undefined"

text \<open>Pokazati da važi: $a^1 = a$.\<close>

lemma stepenuj_jedan:
  shows "a \<Zcat> \<one> = a"
  (*<*) oops (*>*)

text \<open>Pokazati da važi: $a^{(n+m)} = a^n b^m$.\<close>

lemma stepenuj_na_zbir[simp]:
  shows "a \<Zcat> (n \<oplus> m) = a \<Zcat> n \<otimes> a \<Zcat> m"
  (*<*) oops (*>*)

text \<open>Pokazati da važi: $a^{nm} = a^{n^m}$.\<close>

lemma stepenuj_na_proizvod:
  shows "a \<Zcat> (n \<otimes> m) = a \<Zcat> n \<Zcat> m"
  (*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Dodatni primeri.]\<close>

text \<open>Pokazati sledeće teoreme u Isar-u. Kao dodatan izazov, dozvoljeno je korišćenje samo 
      primenjivanje pravila \<open>rule\<close> i \<open>subst\<close> za dokazivanje među koraka, tj. bilo
      kakva automatizacija (\<open>simp, auto, metis, blast, force, fastforce, sladgehammer, ...\<close>) 
      je zabranjena.\<close>

lemma "a \<oplus> Nula = a"
  (*<*) oops (*>*)

lemma "a \<otimes> (Sled b) = a \<otimes> b \<oplus> a"
  (*<*) oops (*>*)

lemma "a \<otimes> b \<otimes> c = a \<otimes> (b \<otimes> c)"
  (*<*) oops (*>*)

lemma "a \<otimes> b = b \<otimes> a"
  (*<*) oops (*>*)

lemma "a \<otimes> (b \<oplus> c) = a \<otimes> b \<oplus> a \<otimes> c"
  (*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
