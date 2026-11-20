Subject: A matching size lower bound for your 11-input median network

Dear Bert Dobbelaere,

I’m Rocco Martino, a master’s student in Cybersecurity at Politecnico di Torino. I’ve been studying the 25-comparator median network for eleven inputs in your catalogue. The manuscript credits you for the construction and gives a computer-assisted lower bound that excludes every fixed network of 24 comparators or fewer, with unrestricted depth.

The proof uses two adjacent Boolean Hamming layers. Selection forces the entire output to be constant on each layer, which makes an extreme input meet at least three comparators. Deleting that input and repeating the argument reduces the lower bound to two nine-input rank-selection problems. A finite certificate for those exclusions is replayed by separate Python and C++ implementations.

The Lean 4.19.0 kernel verifies both nine-input lower bounds and proves the exact-size theorem using your construction. It also checks the decoded certificate for all 26 archived exclusions.

Current paper: https://github.com/HaxelThePenguine/median-of-11/blob/6118662a99fee8b8f881eb4b8048efc173e4649a/paper/main.pdf

Repository and verification sources: https://github.com/HaxelThePenguine/median-of-11

Earlier archived candidate: https://doi.org/10.5281/zenodo.24397716

Are you aware of an earlier proof of size optimality for eleven inputs? I’d also value your opinion on whether the lower-bound argument is sound, particularly the first-reused-wire step and the deletion of the extreme input.

Best regards,

Rocco Martino
