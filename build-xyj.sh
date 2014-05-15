make clean
export PATH=/home/xyj/research/llvm-gcc4.2-2.9-x86_64-linux/bin:$PATH
export PATH=/home/xyj/research/llvm-2.9-github/Release+Asserts/bin:$PATH
export PATH=$PATH:/usr/include/x86_64-linux-gnu

./configure --with-llvm=/home/xyj/research/llvm-2.9-github \
	--with-stp=/home/xyj/research/stp-github/build/install \
	--with-uclibc=/home/xyj/research/klee-uclibc-github \
	--enable-posix-runtime \
	&& make ENABLE_OPTIMIZED=1 -j8
