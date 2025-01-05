package util

func Unclog[T any](c chan T) {
	//non-blockingly receives msgs from channel until none left
	for {
		select {
		case <-c:
			continue
		default:
			return
		}
	}
}
