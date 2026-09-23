// swift-tools-version: 6.0
import PackageDescription

// Installed into .lake by prepare_oracles.py; upstream sources remain unchanged.
let package = Package(
    name: "SwiftOracle",
    dependencies: [
        .package(url: "https://github.com/krzyzanowskim/CryptoSwift.git",
                 revision: "e45a26384239e028ec87fbcc788f513b67e10d8f")
    ],
    targets: [
        .target(name: "PrimitiveTypes"),
        .executableTarget(name: "SwiftOracle", dependencies: [
            "PrimitiveTypes", .product(name: "CryptoSwift", package: "CryptoSwift")
        ], swiftSettings: [.define("DISABLE_TRACING")])
    ]
)
