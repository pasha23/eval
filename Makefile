
all: .tested

.tested: eval32 eval init.ss tests.ss
	./eval32 tests.ss
	./eval tests.ss
	touch .tested

eval32.list: eval32
	objdump -C -S eval32 > eval32.list

eval.list: eval
	objdump -C -S eval > eval.list

eval32: eval.cpp
	g++ -std=c++11 -m32 -ggdb3 -o eval32 eval.cpp

eval: eval.cpp
	g++ -std=c++11 -DUNWIND -ggdb3 -O1 -o eval eval.cpp -lunwind

