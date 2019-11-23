all: eval32 eval

eval32.list: eval32
	objdump -C -S eval32 > eval32.list

eval.list: eval
	objdump -C -S eval > eval.list

eval32: eval.cpp init.ss tests.ss
	g++ -m32 -std=c++17 -ggdb3 -o eval32 eval.cpp
	./eval32 tests.ss

eval: eval.cpp init.ss tests.ss
	g++ -DUNWIND -std=c++17 -ggdb3 -O1 -o eval eval.cpp -lunwind
	./eval tests.ss

