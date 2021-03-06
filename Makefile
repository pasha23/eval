
all: polynomials .tested

.tested: eval32 eval init.ss tests.ss
	rm -f .tested
	./eval32 tests.ss && ./eval tests.ss && touch .tested

polynomials: polynomials.cpp
	g++ -std=c++17 -O1 -o polynomials polynomials.cpp

eval32.list: eval32
	objdump -C -S eval32 > eval32.list

eval.list: eval
	objdump -C -S eval > eval.list

eval32: eval.cpp num.hpp rat.hpp
	g++ -std=c++17 -m32 -ggdb3 -o eval32 eval.cpp

eval: eval.cpp num.hpp rat.hpp
	g++ -std=c++17 -DUNWIND -ggdb3 -o eval eval.cpp -lunwind

