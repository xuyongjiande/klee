make clean
export PATH=/home/xyj/research/my-llvm-gcc4.2-2.9-x86_64-linux/bin:$PATH
export PATH=/home/xyj/research/my-llvm-2.9/Release+Asserts/bin:$PATH
export PATH=$PATH:/usr/include/x86_64-linux-gnu

./configure --with-llvm=/home/xyj/research/my-llvm-2.9 \
	--with-stp=/home/xyj/research/my-stp/build/install \
	--with-uclibc=/home/xyj/research/my-klee-uclibc \
	--enable-posix-runtime \
	&& make ENABLE_OPTIMIZED=1 -j8
