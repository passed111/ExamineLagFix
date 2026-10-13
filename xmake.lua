local plugin_name = "ExamineLagFix"

target(plugin_name)
    add_rules("commonlibf4.plugin", {
        author = "Community",
        description = "Remove the pickup-examine menu stall (scrappable recipe scan and inspect-mode mod list build)"
    })
    add_deps("commonlibf4")
    add_files("src/**.cpp")
    add_defines("NOMINMAX")
