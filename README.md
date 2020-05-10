Z góry przepraszam, to rozwiązanie jest paskudne, ale przyznam szczerze że nie rozumiem jak działają monady, więc używałem map.
Rozwiąznie opiera się na semantyc języka Tiny. 
Id = zbiór indentyfikatorów zmiennych i funkcji
Loc = zbiór lokacji potrzebnyc do przysłaniania zmiennych (w rożwiązniu Loc to Integer)
Data = zbiór reprezentacji funkji i zmiennych
Mamy store i env gdzie:
env: Id -> Loc
store: Loc -> Data 
W programie używam 2 map do przechowywania env i store, w ten sposób reprezentuję stan pamięci.
Zrezygnowałem ze statycznej kontroli typów, instukcji break, continue i krotek. Punkty do zdobycia: 22.
