module github.com/mkuroda13/ConcurrentJanus/runtime

go 1.23.2

require github.com/goccy/go-graphviz v0.2.9

require (
	github.com/disintegration/imaging v1.6.2 // indirect
	github.com/flopp/go-findfont v0.1.0 // indirect
	github.com/fogleman/gg v1.3.0 // indirect
	github.com/golang/freetype v0.0.0-20170609003504-e2365dfdc4a0 // indirect
	github.com/pkg/errors v0.9.1 // indirect
	github.com/tetratelabs/wazero v1.8.2 // indirect
	golang.org/x/image v0.23.0 // indirect
	golang.org/x/text v0.21.0 // indirect
)

replace github.com/mkuroda13/ConcurrentJanus/util => ../util

require github.com/mkuroda13/ConcurrentJanus/util v0.0.0-00010101000000-000000000000
