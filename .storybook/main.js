module.exports = {
  previewHead: (head) => (`
    <link href="https://fonts.googleapis.com/css?family=Cairo:100,200,300,400,500,600,700,800,900" rel="stylesheet">
    <link href="https://fonts.googleapis.com/css?family=Roboto:100,200,300,400,500,600,700,800,900" rel="stylesheet">
    ${head}
  `),
  "stories": [
    "../src/**/*.stories.mdx",
    "../src/**/*.stories.@(js|jsx|ts|tsx)"
  ],
  "addons": [
    'storybook-addon-material-ui5',
    "@storybook/addon-links",
    "@storybook/addon-essentials"
  ],
  "framework": "@storybook/react"
}