%{
#include <stdio.h>
%}
%option noyywrap
%%
Delta { printf("∆"); }
Xi { printf("Ξ"); }
theta { printf("θ"); }
lambda { printf("λ"); }
mu { printf("μ"); }
arithmos { printf("𝔸"); }
N { printf("ℕ"); }
P { printf("ℙ"); }
\/^ { printf("↗"); }
v\/ { printf("↙"); }
\\v { printf("↘"); }
^\\ { printf("↖"); }
\<\< { printf("《"); }
>> { printf("》"); }
\<\| { printf("⦉"); }
\|> { printf("⦊"); }
\|- { printf("⊢"); }
\/\\ { printf("∧"); }
\/ { printf("∨"); }
==> { printf("⇒"); }
\<=> { printf("⇔"); }
not { printf("¬"); }
A { printf("∀"); }
E { printf("∃"); }
x { printf("×"); }
e { printf("∈"); }
@ { printf("⦁"); }
S\\ { printf("⧹"); }
S\|\\ { printf("⨡"); }
S\; { printf("⨟"); }
S>> { printf("⨠"); }
\<--> { printf("↔"); }
--> { printf("→"); }
\/= { printf("≠"); }
\/e { printf("∉"); }
\(\/\) { printf("∅"); }
c_ { printf("⊆"); }
c { printf("⊂"); }
u { printf("∪"); }
n { printf("∩"); }
(-) { printf("⊖"); }
uu { printf("⋃"); }
nn { printf("⋂"); }
F { printf("𝔽"); }
\|--> { printf("↦"); }
\; { printf("⨾"); }
o { printf("∘"); }
\<: { printf("◁"); }
:> { printf("▷"); }
\<-: { printf("⩤"); }
:-> { printf("⩥"); }
~ { printf("∼"); }
\(\| { printf("⦇"); }
\|\) { printf("⦈"); }
\(\+\) { printf("⊕"); }
-\|-> { printf("⇸"); }
>-\|-> { printf("⤔"); }
>--> { printf("↣"); }
-\|->> { printf("⤀"); }
-->> { printf("↠"); }
>-->> { printf("⤖"); }
-\|\|-> { printf("⇻"); }
>-\|\|-> { printf("⤕"); }
Z { printf("ℤ"); }
\<= { printf("≤"); }
>= { printf("≥"); }
\< { printf("〈"); }
> { printf("〉"); }
\^ { printf("⁀"); }
\/\| { printf("↿"); }
\|\\ { printf("↾"); }
. { printf(yytext); }
%%
int main() {
  yylex();
}
