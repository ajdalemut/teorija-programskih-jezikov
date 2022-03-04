# NAVODILA ZA PRVO DOMAČO NALOGO

Naloga obsega dve razširitvi jezika Lambda, ki ste ga spoznali med predavanji.

Za oddajo naloge si podvojite repozitorij (*fork*) na vaš uporabniški račun. Razširitve jezika in dodatne datoteke nato dodajte na vaš repozitorij (prav tako na vejo `domaca-naloga-01`), na spletni učilnici pa oddatje zgolj povezavo do vašega repozitorija.

Cilj domače naloge so izključno razširitve jezike, zato pri karkšnihkoli problemih z izgradnjo jezika Lambda pošljite e-mail, da problem čimprej rešimo.

### Linux & Mac

Za izgradnjo jezika v konzoli pojdite do mape `domaca-naloga-01/lambda` in v njej poženite `ocamlbuild lambda.native`.

Prevajalnik vam bo zgradil datoteko `lambda.native`, ki jo uporabljate kot 

```./lambda.native eager ime_datoteke.lam```

(za leno izvajanje `eager` zamenjajte z `lazy`).

### Windows

Če ste OCaml namestili preko povezave na spletni učilnici, je uporaba rahlo bolj zapletena. Repozitorij vsebuje datoteko `tasks.json`, v kateri so definirani VSCode taski `Compile Lambda` in `Lambda Eager/Lazy`. Poženete jih tako, da odprete VSCode meni (`ctrl+shift+p`), izberete možnost `Run Task` in izberete želen task.

**Če ne želite uporabljati VSCode imate v `tasks.json` hiter komentar ukazov, ki jih lahko nato prilagodite po svoje.**

VSCode taske zazna zgolj če se mapa `.vscode` nahaja na zgornjem nivoju (torej da imate v VSCode odprto zgolj mapo repozitorija (ukaz `Open Folder` v VSCode meniju)).

Preden bodo taski delovali, jih morate nastaviti na vaš sistem.

Vse pojavitve `???` zamenjajte z imenom vašega računalnika (npr. `ZigaPC`)
in vse pojavitve `!!!` zamenjajte z inštalirano verzijo OCamla (npr. `4.09.0+mingw64c`).

Najprej v raziskovalcu preverite, da sta poti
- `C:\\OCaml64\\usr\\local\\bin\\` 
- `C:\\OCaml64\\home\\???\\.opam\\!!!\\bin\\` 

veljavni (morda boste morali spremeniti pot na 32-bitno različico glede na vašo namestitev).

Task `Compile Lambda` bi moral delovati kjerkoli iz mape, `Lambda Eager` pa vam v lambdi zažene trenutno odprto datoteko.

**Kadar vam Lambda javi napako `End_of_file`, morate spremeniti 'end of line sequence'**. To lahko storite v VSCode meniju (ukaz `Change End of Line Sequence`) ali pa v spodnjem desnem kotu okna, kjer je izbrana opcija `CRLF`, ki jo spremenite na `LF`.

## RAZŠIRITEV S PARI IN SEZNAMI

Jezik Lambda smo na vajah idejno že razširili s pari in seznami. Tako pari kot seznami so že dodani v parser in sintakso jezika. 

Dodan je konstruktor za pare `{e1, e2} ~ Pair (e1, e2)`, prazen seznam `[] ~ Nil` in konstruiran seznam `e :: es ~ Cons (e, es)` (seznam več elementov se mora končati s praznim seznamom, torej `1::2::3::[]`). Prav tako sta dodani projekciji na komponente `FST e ~ Fst e` in `SND e ~ Snd e` in pa `MATCH e WITH | [] -> e1 | x :: xs -> e2 ~ Match (e, e1, x, xs, e2)`. 

Vaša naloga je:
1. V `syntax.ml` dopolnite substitucijo za nove konstrukte.
2. Dopolnite evaluator `eval.ml` za nove konstrukte. Pomembno je, da pravilno deluje za smiselne programe (torej ne rabite skrbeti kaj se zgodi s programom `FST 1`).
3. V datoteko `map.lam` napišite funkcijo `map` in jo uporabite na primeru.
4. V datoteko `split.lam` napišite funkicjo `split` in jo uporabite na primeru.

(opis funkcij `map` in `split` lahko poiščete v Ocaml Documentaciji https://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html) 

## RAZŠIRITEV Z LENIM IZVAJANJEM

Jeziku Lambda (z dodanimi pari in seznami) dodajte leno izvajanje. V datoteki `lazyEval.ml` se nahaja kopija `eval.ml`, ki se uporabi kadar lambdo pokličemo z besedo `lazy`.

Vaša naloga je:
1. Popravite izvajanje funkcij na leno izvajanje.
2. Dodajte leno izvajanje za pare in sezname.
3. V datoteko `lazy_good.lam` napišite program, ki se z lenim izvajanjem izvede mnogo hitreje. Nato v datoteko `lazy_bad.lam` napišite program, ki se z lenim izvajanjem izvede mnogo počasneje.
4. **Dodatni izziv:** V datoteko `substitution_broken.lam` napišite primer, kjer trenutna substitucija jezika Lambda naredi napako. Substitucijo nato popravite.
