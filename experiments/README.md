# Mediana di 11 valori · 19 novembre 2026

Minimo dimostrato nel modello richiesto: **25 comparatori**. La costruzione è pubblica. Il pacchetto contiene un certificato del limite inferiore e un verificatore indipendente, con una spiegazione in PROOF.md. La prova è computazionale e non è stata sottoposta a peer review.

## Ripetere il controllo decisivo

Dalla radice del repository, con Python 3.10 o successivo:

```sh
python3 verify.py
python3 verify.py median11_25.json
python3 check_certificate.py
python3 corruption.py
```

Il primo programma verifica le tre reti di seeds.json su ogni input. Il secondo verifica il file della soluzione. Il terzo deve terminare con `ACCEPT median(11) >= 25; 174008 proof nodes`. Il quarto deve respingere due certificati corrotti e una rete da 24 ottenuta tagliando la baseline. Nel file della soluzione le coppie sono in ordine di esecuzione, con indici da 0. L’uscita è il filo 5. Per rigenerare l’intero certificato usare una directory distinta:

```sh
python3 lower.py --output rebuilt > rebuilt.jsonl
python3 check_certificate.py rebuilt
```

## Riprodurre la ricerca di costruzioni

Ambiente utilizzato: Linux x86-64, Python 3.12.14, libz3 4.13.3 e g++ 14.2. I comandi di questa sezione richiedono la libreria condivisa Z3 rilevabile da Python e un compilatore C++17. Per la sola verifica finale bastano i comandi della prima sezione.

```sh
cd experiments
python3 synth.py control > control.new.jsonl
python3 synth.py small --rlimit 3000000 > small.new.jsonl
python3 synth.py wide --rlimit 1800000 > wide.new.jsonl
python3 synth.py global --rlimit 180000000 > global.new.jsonl
python3 global_full.py
g++ -std=c++17 -O3 -march=native exact.cpp -o exact
python3 templates.py > templates.new.txt
./exact < templates.new.txt > exact.new.log
g++ -std=c++17 -O3 -march=native anneal.cpp -o anneal
./anneal 11025 160 < 11-25.pairs > anneal25.new.log
./anneal 11026 160 < 11-26.pairs > anneal26.new.log
python3 repair.py > repair.new.txt
./exact < repair.new.txt > repair.new.log
```

Ogni posizione libera nell’encoding SAT sceglie 0≤i≤j≤10. i=j rappresenta un passo vuoto. Il modello globale ha 24 posizioni libere, tutte le coppie e nessun limite di profondità. Gli input in un giro SAT vengono simulati in parallelo sui bit di un vettore. Il CEGIS parte con 8 campioni per ciascuno dei pesi 5 e 6 e aggiunge fino a 12 controesempi per giro. Ogni modello viene controllato sui 2.048 casi. global_full.py usa simultaneamente tutti i 924 casi di confine. Il limite di risorse è per singola chiamata a Z3 e può produrre unknown. La formula globale completa è in global24.smt2.

Il generatore delle finestre emette sia l’ordine originale sia un riordino riproducibile mediante scambi tra comparatori disgiunti. Le coppie di finestre libere sono esplicitate in wide.jsonl. exact.cpp enumera ciascuna metà di un modello locale in entrambe le direzioni. L’enumerazione in avanti conserva gli stati raggiungibili dei pesi 5 e 6, quella all’indietro gli stati che il suffisso manderebbe in errore. Una coppia di metà è valida esattamente quando questi insiemi sono disgiunti. Tutte le posizioni libere ammettono anche l’identità. Le etichette nei log identificano istanze che possono sovrapporsi.

## Risultati registrati

| Esperimento | Risultato |
|---|---|
| Reti pubblicate (9,19), (11,25), (11,26) | 0 errori su 512, 2.048 e 2.048 input |
| SAT sulle finestre contigue di lunghezza 3, taglia obiettivo 24 | 94 UNSAT |
| SAT su finestre di lunghezza 6 e finestre separate | 2 UNSAT, 30 unknown |
| SAT globale con controesempi | SAT sui primi 16, 28 e 40 esempi, unknown a 52 |
| SAT globale con tutti i casi di confine | unknown |
| Enumerazione esatta delle finestre, incluse finestre con 5 posizioni libere | 206 esclusioni e 2 controlli positivi, entrambi verificati |
| Simulated annealing, 160 riavvii per ciascuna seed e 24.000 proposte a riavvio | Migliori reti da 24 con 6 errori ciascuna, anche sul test completo |
| Riparazione di ognuna di queste due reti, liberando qualsiasi terna di posizioni | 4.048 modelli esclusi esattamente |
| Certificato globale separato | 26 proposizioni, 174.008 nodi accettati |

I processi stocastici possono variare cambiando toolchain. I due candidati da 24 sono nelle ultime righe dei rispettivi log. Per il primo falliscono le maschere decimali 115, 693, 709, 1338, 1354, 1675. Per il secondo 283, 718, 880, 1182, 1428, 1748. Il bit meno significativo corrisponde al filo 0.

## Fonti

* Bert Dobbelaere, costruzioni pubbliche verificate: https://bertdobbelaere.github.io/median_networks.html
* Generalised Superintelligence, 16 novembre 2026, tabella delle taglie per la selezione fino a 9 ingressi: https://generalised.si/research/moore-bound-defect-two . I valori utilizzati nell’induzione sono ricontrollati dal certificato allegato.
