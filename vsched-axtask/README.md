# 在 Arceos 中使用 Vsched

## 前提

Vsched 主要用于在多进程、地址空间中进行任务切换，因此，Arceos 需要使能 `paging` trait。

## 地址映射

axmm 中存在对应的映射函数

直接将 libvsched.so 内联到内核中，这里只能保证代码段是没有问题，共享库使用的数据段还需要额外分配。

