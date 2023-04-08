import numpy as np


def partition(arr, left, right, e):
    """
    Partition array around element e
    :param arr: array
    :param l: left index
    :param r: right index
    :param e: element to partition around
    :return: partitioned array

    This returns an array whose elements are less than e on the left,
    greater than e on the right and those elements equal to e are in the middle
    """
    i = left
    j = right
    while i < j:
        if arr[i] < e:
            i += 1
        if arr[j] > e:
            j -= 1
        if arr[i] > e and arr[j] < e:
            arr[i], arr[j] = arr[j], arr[i]
            i += 1
            j -= 1
        elif arr[i] == e and arr[j] < e:
            arr[i], arr[j] = arr[j], arr[i]
            i += 1
        elif arr[i] > e and arr[j] == e:
            arr[i], arr[j] = arr[j], arr[i]
            j -= 1
        elif arr[i] == e and arr[j] == e:
            i_ = i
            while i_ < j and arr[i_] == e:
                i_ += 1
            if i_ == j:
                break
            else:
                if arr[i_] < e:
                    arr[i_], arr[i] = arr[i], arr[i_]
                else:  # arr[i_] > e
                    arr[i_], arr[j] = arr[j], arr[i_]
                    j -= 1
                i += 1
        else:
            # do nothing
            pass

    # Search for the first element equal to e
    p = left
    q = left
    while p < right and arr[p] < e:
        p += 1

    q = p

    while q < right and arr[q] == e:
        q += 1

    return {
        'p': p,
        'q': q,
        'v': arr
    }


def sort_array(arr, num):
    n = len(arr)
    i = 0
    j = n - 1
    k = 0
    while k <= j:
        if arr[k] < num:
            arr[i], arr[k] = arr[k], arr[i]
            i += 1
            k += 1
        elif arr[k] > num:
            arr[j], arr[k] = arr[k], arr[j]
            j -= 1
        else:
            k += 1
    return arr




if __name__ == '__main__':
    # arr = np.random.randint(0, 10, 15)
    arr = [0, 7, 3, 8, 8, 0, 5, 8, 6, 0, 8, 1, 3, 5, 5, 8]
    print(f'Array: {arr}')
    # ret = partition(arr, 0, len(arr) - 1, e=5)
    # print(f'Partitioned array: {ret["v"]}')
    # print(f'p: {ret["p"]}')
    # print(f'q: {ret["q"]}')
    ret = sort_array(arr, 5)
    print(f'Sorted array: {ret}')
