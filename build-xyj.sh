make clean
export PATH=`pwd`/Downloads/llvm-gcc4.2-2.9-x86_64-linux/bin:$PATH
export PATH=`pwd`/Downloads/llvm-2.9/Release+Asserts/bin:$PATH
export PATH=$PATH:/usr/include/x86_64-linux-gnu

./configure --with-llvm=./Downloads/llvm-2.9 \
	--with-stp=./Downloads/stp/build \
	--with-uclibc=./Downloads/klee-uclibc \
	--enable-posix-runtime \
	&& make ENABLE_OPTIMIZED=1 -j8
