import { muiTheme } from 'storybook-addon-material-ui5'

export const parameters = {
  actions: { argTypesRegex: "^on[A-Z].*" },
  controls: {
    matchers: {
      color: /(background|color)$/i,
      date: /Date$/,
    },
  },
  previewTabs: {
    canvas: {
      hidden: true,
    }
  },
  addons: {
    disable: true,
  },
  enableShortcuts: false
}

export const decorators = [
  muiTheme()
];
