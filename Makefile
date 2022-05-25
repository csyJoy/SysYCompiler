debug:
	docker run -p 1234:1234 -it -v ~/SysYCompiler:/root/compiler compiler:v1 autotest -riscv -s total_perf /root/compiler
test:
